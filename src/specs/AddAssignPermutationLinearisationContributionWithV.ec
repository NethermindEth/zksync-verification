pragma Goals:printall.

require import AllCore.
require        Constants.
require import EllipticCurve.
require import Field.
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
      var intermediateValue, intermediateValue_1, factor, buffer_point, ret_point, ret_factor, ret;
      var buffer_point_opt;
      var failed;
      var _4, _6, _7, _9, _10, _12, _13, _17, _26, _27, _30, _31, _34, _35;

      _4 <- ((state_z * state_beta %% Constants.R) + state_gamma) %% Constants.R;
      intermediateValue <- (_4 + stateOpening0AtZ) %% Constants.R;
      factor <- (state_alpha4 * intermediateValue) %% Constants.R;
      _6 <- ((state_z * state_beta %% Constants.R) * Constants.NON_RESIDUE_0 %% Constants.R);
      _7 <- (_6 + state_gamma) %% Constants.R;
      intermediateValue <- (_7 + stateOpening1AtZ) %% Constants.R;
      factor <- (factor * intermediateValue %% Constants.R);
      _9 <- ((state_z * state_beta %% Constants.R) * Constants.NON_RESIDUE_1 %% Constants.R);
      _10 <- (_9 + state_gamma) %% Constants.R;
      intermediateValue <- (_10 + stateOpening2AtZ) %% Constants.R;
      factor <- (factor * intermediateValue) %% Constants.R;
      _12 <- (((state_z * state_beta) %% Constants.R) * Constants.NON_RESIDUE_2) %% Constants.R;
      _13 <- (_12 + state_gamma) %% Constants.R;
      intermediateValue <- (_13 + stateOpening3AtZ) %% Constants.R;
      factor <- (factor * intermediateValue) %% Constants.R;
      _17 <- (state_l0AtZ * state_alpha5) %% Constants.R;
      factor <- (factor + _17) %% Constants.R;
      ret_factor <- (factor * state_v) %% Constants.R;

      factor <- (state_alpha4 * state_beta) %% Constants.R;
      factor <- (factor * state_gp_omega) %% Constants.R;
      _26 <- (poly0_opening * state_beta) %% Constants.R;
      _27 <- (_26 + state_gamma) %% Constants.R;
      intermediateValue_1 <- (_27 + stateOpening0AtZ) %% Constants.R;
      factor <- (factor * intermediateValue_1) %% Constants.R;
      _30 <- (poly1_opening * state_beta) %% Constants.R;
      _31 <- (_30 + state_gamma) %% Constants.R;
      intermediateValue_1 <- (_31 + stateOpening1AtZ) %% Constants.R;
      factor <- (factor * intermediateValue_1) %% Constants.R;
      _34 <- (poly2_opening * state_beta) %% Constants.R;
      _35 <- (_34 + state_gamma) %% Constants.R;
      intermediateValue_1 <- (_35 + stateOpening2AtZ) %% Constants.R;
      factor <- (factor * intermediateValue_1) %% Constants.R;
      factor <- (factor * state_v) %% Constants.R;

      buffer_point_opt <@ PointMulIntoDest.mid(vk_permutation_3.`1, vk_permutation_3.`2, factor);
      failed <- is_none buffer_point_opt;
      buffer_point <- odflt (0,0) buffer_point_opt;

      ret_point <@ PointSubAssign.mid(point, buffer_point);
      if (failed \/ is_none ret_point) {
        ret <- None;
      } else {
        ret <- Some (ret_factor, odflt (0,0) ret_point);
      }

      return ret;
  }

  proc high_encapsulated(point: g, vk_permutation_3: g, stateOpening0AtZ: FieldR.F, stateOpening1AtZ: FieldR.F, stateOpening2AtZ: FieldR.F, stateOpening3AtZ: FieldR.F, state_beta: FieldR.F, state_v: FieldR.F, state_z: FieldR.F, state_gamma: FieldR.F, state_alpha4: FieldR.F, state_alpha5: FieldR.F, state_gp_omega: FieldR.F, state_l0AtZ: FieldR.F, poly0_opening: FieldR.F, poly1_opening: FieldR.F, poly2_opening: FieldR.F): FieldR.F * g = {
      var buffer_point, ret_point, ret_factor;

      ret_factor <- (
        state_alpha4 * (state_z * state_beta + state_gamma + stateOpening0AtZ) *
        (state_z * state_beta * (FieldR.inF Constants.NON_RESIDUE_0) + state_gamma + stateOpening1AtZ) *
        (state_z * state_beta * (FieldR.inF Constants.NON_RESIDUE_1) + state_gamma + stateOpening2AtZ) *
        (state_z * state_beta * (FieldR.inF Constants.NON_RESIDUE_2) + state_gamma + stateOpening3AtZ) +
        state_l0AtZ * state_alpha5
      ) * state_v;

      buffer_point <@ PointMulIntoDest.high(vk_permutation_3, (
        state_alpha4 * state_beta * state_gp_omega *
        (poly0_opening * state_beta + state_gamma + stateOpening0AtZ) *
        (poly1_opening * state_beta + state_gamma + stateOpening1AtZ) *
        (poly2_opening * state_beta + state_gamma + stateOpening2AtZ) *
        state_v
      ));
      ret_point <@ PointSubAssign.high(point, buffer_point);
      return (ret_factor, ret_point);
  }

  proc high(point: g, vk_permutation_3: g, stateOpening0AtZ: FieldR.F, stateOpening1AtZ: FieldR.F, stateOpening2AtZ: FieldR.F, stateOpening3AtZ: FieldR.F, state_beta: FieldR.F, state_v: FieldR.F, state_z: FieldR.F, state_gamma: FieldR.F, state_alpha4: FieldR.F, state_alpha5: FieldR.F, state_gp_omega: FieldR.F, state_l0AtZ: FieldR.F, poly0_opening: FieldR.F, poly1_opening: FieldR.F, poly2_opening: FieldR.F): FieldR.F * g = {
      var ret_point, ret_factor;

      ret_factor <- (
        state_alpha4 * (state_z * state_beta + state_gamma + stateOpening0AtZ) *
        (state_z * state_beta * (FieldR.inF Constants.NON_RESIDUE_0) + state_gamma + stateOpening1AtZ) *
        (state_z * state_beta * (FieldR.inF Constants.NON_RESIDUE_1) + state_gamma + stateOpening2AtZ) *
        (state_z * state_beta * (FieldR.inF Constants.NON_RESIDUE_2) + state_gamma + stateOpening3AtZ) +
        state_l0AtZ * state_alpha5
      ) * state_v;

      ret_point <- point + (G.inv ((
        state_alpha4 * state_beta * state_gp_omega *
        (poly0_opening * state_beta + state_gamma + stateOpening0AtZ) *
        (poly1_opening * state_beta + state_gamma + stateOpening1AtZ) *
        (poly2_opening * state_beta + state_gamma + stateOpening2AtZ) *
        state_v
      ) * vk_permutation_3));
      return (ret_factor, ret_point);
  }
}.

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

lemma addAssignPermutationLinearisationContributionWithV_low_pspec_revert :
    phoare [
      AddAssignPermutationLinearisationContributionWithV.low :
      Primops.reverted ==>
      Primops.reverted
    ] = 1%r.
    proof.
      proc.
      call pointSubAssign_low_pspec_revert.
      call pointMulIntoDest_low_pspec_revert.
      inline*. wp. skip. by progress.
qed.
   

op addAssignPermutation_memory_footprint
(mem_0: mem)
(x64 x64' x96: uint256)
(coeff: uint256)
(buffer_point ret_point: int*int)
(p1_addr p2_addr: uint256) =
  let mem_1 = store mem_0 COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF coeff in
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
      W256.of_int 128 <= dest{1} + W256.of_int 32 /\
      W256.of_int 32 <= - (dest{1} + W256.of_int 32) /\
      W256.of_int 32 <= dest{1} - COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /\
      W256.of_int 64 <= COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF - dest{1} /\
      W256.of_int 64 <= dest{1} - QUERIES_BUFFER_POINT_SLOT /\
      W256.of_int 64 <= QUERIES_BUFFER_POINT_SLOT - dest{1} /\
      W256.of_int 64 <= (dest{1} + W256.of_int 32) - QUERIES_BUFFER_POINT_SLOT /\ (*easier to put these in here and prove them once we have a conrete value for dest *)
      W256.of_int 32 <= QUERIES_BUFFER_POINT_SLOT + W256.of_int 32 - (dest{1} + W256.of_int 32) /\
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
        0 <= f < Constants.R /\
        0 <= p.`1 < Constants.Q /\
        0 <= p.`2 < Constants.Q /\
        res{2} = Some (f, p) /\
        exists (x64 x64' x96: uint256) (buffer_p: int*int),
        Primops.memory{1} = addAssignPermutation_memory_footprint
          mem_0
          x64 x64' x96
          (W256.of_int f)
          buffer_p p
          dest_l QUERIES_BUFFER_POINT_SLOT
      )  
    ].
    proof.
      proc.

      seq 5 1: (
        #pre /\
        state_alpha4{2} = alpha4_r /\
        state_alpha4{2} = W256.to_uint factor{1} /\
        state_beta{2} = W256.to_uint _1{1} /\
        state_z{2} = W256.to_uint _3{1} /\
        state_gamma{2} = W256.to_uint gamma{1} /\
        _4{2} = W256.to_uint _4{1}
      ).
      inline*. wp. skip. progress.
      rewrite /addmod /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK. rewrite mod_R_W256_mod_R.
      rewrite W256.of_uintK. rewrite mod_R_W256_mod_R.
      reflexivity.
      
      seq 1 1: (
        #pre /\
        intermediateValue{2} = W256.to_uint intermediateValue{1}
      ).
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK. rewrite mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: (
        dest_l = dest{1} /\
        128 <= W256.to_uint dest{1} /\
        64 <= W256.to_uint (-dest{1}) /\
        W256.of_int 128 <= dest{1} + W256.of_int 32 /\
        W256.of_int 32 <= - (dest{1} + W256.of_int 32) /\
        W256.of_int 32 <= dest{1} - COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /\
        W256.of_int 64 <= COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF - dest{1} /\
        W256.of_int 64 <= dest{1} - QUERIES_BUFFER_POINT_SLOT /\
        W256.of_int 64 <= QUERIES_BUFFER_POINT_SLOT - dest{1} /\
        W256.of_int 64 <= (dest{1} + W256.of_int 32) - QUERIES_BUFFER_POINT_SLOT /\
        W256.of_int 32 <= QUERIES_BUFFER_POINT_SLOT + W256.of_int 32 - (dest{1} + W256.of_int 32) /\
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
        Primops.memory{1} = mem_0 /\
        state_alpha4{2} = alpha4_r /\
        state_beta{2} = W256.to_uint _1{1} /\
        state_z{2} = W256.to_uint _3{1} /\
        state_gamma{2} = W256.to_uint gamma{1} /\
        _4{2} = W256.to_uint _4{1} /\
        intermediateValue{2} = W256.to_uint intermediateValue{1} /\
        factor{2} = W256.to_uint factor{1}
      ).
      wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK. rewrite mod_R_W256_mod_R.
      rewrite H20.
      reflexivity.

      seq 1 1: (
        #pre /\
        _6{2} = W256.to_uint _6{1}
      ).
      wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK. rewrite mod_R_W256_mod_R.      
      rewrite H21 H20 Constants.non_residue_0_int.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: (
        #pre /\
        _7{2} = W256.to_uint _7{1}
      ).
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite H22. rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.
      
      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.      

      seq 1 1: (
        #pre /\
        _9{2} = W256.to_uint _9{1}
      ).
      wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R. rewrite H20 H21.
      rewrite W256.of_uintK mod_R_W256_mod_R. rewrite Constants.non_residue_1_int.
      reflexivity.

      seq 1 1: (
        #pre /\
        _10{2} = W256.to_uint _10{1}
      ).
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R H22.
      reflexivity.

      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.      

      seq 1 1: (
        #pre /\
        _12{2} = W256.to_uint _12{1}
      ).
      wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite H20 H21 Constants.non_residue_2_int.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: (
        #pre /\
        _13{2} = W256.to_uint _13{1}
      ).
      wp. skip. progress.
      rewrite /addmod H22 -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.
 
      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 3 1: (
        #pre /\
        state_l0AtZ{2} = W256.to_uint l0AtZ{1} /\
        _16{1} = W256.of_int alpha5_r /\
        _17{2} = W256.to_uint _17{1}
      ).
      inline*. wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 3 1: (
        dest_l = dest{1} /\
        128 <= W256.to_uint dest{1} /\
        64 <= W256.to_uint (-dest{1}) /\
        W256.of_int 128 <= dest{1} + W256.of_int 32 /\
        W256.of_int 32 <= - (dest{1} + W256.of_int 32) /\
        W256.of_int 32 <= dest{1} - COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /\
        W256.of_int 64 <= COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF - dest{1} /\
        W256.of_int 64 <= dest{1} - QUERIES_BUFFER_POINT_SLOT /\
        W256.of_int 64 <= QUERIES_BUFFER_POINT_SLOT - dest{1} /\
        W256.of_int 64 <= (dest{1} + W256.of_int 32) - QUERIES_BUFFER_POINT_SLOT /\
        W256.of_int 32 <= QUERIES_BUFFER_POINT_SLOT + W256.of_int 32 - (dest{1} + W256.of_int 32) /\
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
        0 <= ret_factor{2} < Constants.R /\
        Primops.memory{1} = store mem_0 COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int ret_factor{2})
      ).
      inline*. wp. skip. progress.
      by rewrite /Constants.R; exact modz_ge0.
      by rewrite /Constants.R; exact ltz_pmod.
      by rewrite /mulmod -Constants.R_int; progress.

      seq 3 1: (
        #pre /\
        _20{1} = W256.of_int beta_r /\
        _21{1} = W256.of_int alpha4_r /\
        factor{2} = W256.to_uint factor{1}
      ).
      inline*. wp. skip. progress.
      rewrite load_store_diff.
        by rewrite /STATE_BETA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /STATE_BETA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        reflexivity.
      rewrite load_store_diff.
        by rewrite /STATE_POWER_OF_ALPHA_4_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /STATE_POWER_OF_ALPHA_4_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        reflexivity.
      rewrite /mulmod. simplify.
      rewrite load_store_diff.
        by rewrite /STATE_POWER_OF_ALPHA_4_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /STATE_POWER_OF_ALPHA_4_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite load_store_diff.
        by rewrite /STATE_BETA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /STATE_BETA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite W256.of_uintK -Constants.R_int mod_R_W256_mod_R.
      reflexivity.

      seq 2 1: (
        #pre /\
        _23{1} = W256.of_int state_gp_omega{2}
      ).
      inline*. wp. skip. progress.
      rewrite load_store_diff.
        by rewrite /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.
      rewrite load_store_diff.
        by rewrite /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        reflexivity.


      seq 4 1: (
        #pre /\
        beta'{1} = W256.of_int beta_r /\
        gamma_1{1} = W256.of_int gamma_r /\
        poly0_opening{2} = W256.to_uint _25{1} /\
        _26{2} = W256.to_uint _26{1}
      ).
      inline*. wp. skip. progress.
      rewrite load_store_diff.
        by rewrite /STATE_BETA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /STATE_BETA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        reflexivity.
      rewrite load_store_diff.
        by rewrite /STATE_GAMMA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /STATE_GAMMA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        reflexivity.
      rewrite load_store_diff.
        by rewrite /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        reflexivity.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      rewrite load_store_diff.
        by rewrite /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite load_store_diff.
        by rewrite /STATE_BETA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /STATE_BETA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      reflexivity.


      seq 1 1: (
        #pre /\
        _27{2} = W256.to_uint _27{1}
      ).
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: (
        #pre /\
        intermediateValue_1{2} = W256.to_uint intermediateValue_1{1}
      ).
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 2 1: (
        #pre /\
        poly1_opening{2} = W256.to_uint _29{1} /\
        _30{2} = W256.to_uint _30{1}
      ).
      inline*. wp. skip. progress.
      rewrite /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF load_store_diff; progress.
      rewrite /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF load_store_diff; progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: (#pre /\ _31{2} = W256.to_uint _31{1}).
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 2 1: (
        #pre /\
        poly2_opening{2} = W256.to_uint _33{1} /\
        _34{2} = W256.to_uint _34{1}
      ).
      inline*. wp. skip. progress.
      rewrite /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF load_store_diff; progress.
      rewrite /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF load_store_diff; progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: (
        #pre /\
        _35{2} = W256.to_uint _35{1}
      ).
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.      


      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /addmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 1 1: #pre.
      wp. skip. progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.

      seq 2 1: (
        #pre /\
        state_v{2} = W256.to_uint _36{1}
      ).
      inline*. wp. skip. progress.
      rewrite /STATE_V_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF load_store_diff; progress.
      rewrite /mulmod -Constants.R_int. simplify.
      rewrite W256.of_uintK mod_R_W256_mod_R.
      reflexivity.
      by rewrite /STATE_V_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF load_store_diff; progress.

      seq 1 3: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          dest_l = dest{1} /\
          128 <= W256.to_uint dest{1} /\
          64 <= W256.to_uint (-dest{1}) /\
          W256.of_int 128 <= dest{1} + W256.of_int 32 /\
          W256.of_int 32 <= - (dest{1} + W256.of_int 32) /\
          0 <= buffer_point{2}.`1 < FieldQ.p /\
          0 <= buffer_point{2}.`2 < FieldQ.p /\
          point{2}.`1 = W256.to_uint (load mem_0 dest{1}) /\
          point{2}.`2 = W256.to_uint (load mem_0 (dest{1} + W256.of_int 32)) /\
          0 <= point{2}.`1 < Constants.Q /\
          0 <= point{2}.`2 < Constants.Q /\
          W256.of_int 32 <= dest{1} - COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /\
          W256.of_int 64 <= COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF - dest{1} /\
          W256.of_int 64 <= dest{1} - QUERIES_BUFFER_POINT_SLOT /\
          W256.of_int 64 <= QUERIES_BUFFER_POINT_SLOT - dest{1} /\
          W256.of_int 64 <= (dest{1} + W256.of_int 32) - QUERIES_BUFFER_POINT_SLOT /\
          W256.of_int 32 <= QUERIES_BUFFER_POINT_SLOT + W256.of_int 32 - (dest{1} + W256.of_int 32) /\
          0 <= ret_factor{2} < Constants.R /\
          exists (x0 x32 x64: uint256), Primops.memory{1} = store(store(store(store(store(store mem_0
                    COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int ret_factor{2}))
                  W256.zero x0)
                (W256.of_int 32) x32)
              (W256.of_int 64) x64)
            QUERIES_BUFFER_POINT_SLOT (W256.of_int buffer_point{2}.`1))
          (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32) (W256.of_int buffer_point{2}.`2)
        )
      ).
      exists* vk_permutation_3{2}, factor{2}, Primops.memory{1}.
      elim*=> vk_permutation_3_r factor_r memory_l.
      wp. call (pointMulIntoDest_low_equiv_mid vk_permutation_3_r.`1 vk_permutation_3_r.`2 factor_r VK_PERMUTATION_3_X_SLOT QUERIES_BUFFER_POINT_SLOT memory_l).
      skip. progress.
      by rewrite H15; exact to_uint_ge_zero.
      by rewrite -Constants.q_eq_fieldq_p; exact H16.
      by rewrite H17; exact to_uint_ge_zero.
      by rewrite -Constants.q_eq_fieldq_p; exact H18.
      exact to_uint_ge_zero.
      exact to_uint_lt_mod.
      by rewrite /VK_PERMUTATION_3_X_SLOT W256.of_intN'; progress.
      by rewrite /VK_PERMUTATION_3_X_SLOT; progress; rewrite W256.of_intN'; progress.
      rewrite load_store_diff.
      by rewrite /VK_PERMUTATION_3_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      by rewrite /VK_PERMUTATION_3_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      by rewrite H15; progress.
      rewrite load_store_diff.
      by rewrite /VK_PERMUTATION_3_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      by rewrite /VK_PERMUTATION_3_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      by rewrite H17; progress.
      case H39. progress.
      exact FieldQ.ge0_asint.
      exact FieldQ.gtp_asint.
      exact FieldQ.ge0_asint.
      exact FieldQ.gtp_asint.
      exists (W256.of_int vk_permutation_3{2}.`1).
      exists (W256.of_int vk_permutation_3{2}.`2).
      exists factor{1}.
      reflexivity.

      by progress.

      (* final segment *)

      exists* Primops.reverted{1}. elim*=> reverted.
      case reverted.
      progress.
      call{1} pointSubAssign_low_pspec_revert.
      inline*. wp. skip. progress. smt ().
      exists ret_factor{2}. smt ().

      progress. wp.
      exists* Primops.memory{1}, dest{1}, point{2}, buffer_point{2}.
      elim*=> memory_L dest_L point_R buffer_point_R.
      call (pointSubAssign_low_equiv_mid_fixed memory_L dest_L QUERIES_BUFFER_POINT_SLOT point_R buffer_point_R).
      progress. skip. progress.
      by rewrite /QUERIES_BUFFER_POINT_SLOT W256.of_intN'; progress.
      rewrite load_store_diff.
        exact uint256_le_sub_add_32.
        rewrite uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64)). by progress. assumption.
      rewrite load_store_diff.
        apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
        apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
      rewrite load_store_diff.
        apply diff_64. apply uint256_le_of_le. by progress.
        apply diff_neg_64. apply uint256_le_of_le. by progress. apply uint256_le_of_le. simplify. apply (le_trans _ 64). by progress. assumption.
      rewrite load_store_diff.
        apply diff_32. apply uint256_le_of_le. by progress.
        apply diff_neg_32. apply uint256_le_of_le. by progress. apply uint256_le_of_le. simplify. apply (le_trans _ 64). by progress. assumption.
      rewrite load_store_diff.
        apply diff_0. apply uint256_le_of_le. by progress.
        apply diff_neg_0. apply uint256_le_of_le. by progress. apply uint256_le_of_le. simplify. apply (le_trans _ 64). by progress. assumption.
      rewrite load_store_diff.
        assumption.
        apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
        rewrite H9. reflexivity.
      rewrite load_store_diff.
        apply uint256_le_sub_add_32. assumption. assumption.
      rewrite load_store_diff.
        apply uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64)). by progress. assumption.
        apply uint256_le_sub_add_32. assumption.
      rewrite load_store_diff.
        apply diff_64. assumption.
        apply diff_neg_64. assumption. assumption.
      rewrite load_store_diff.
        apply diff_32. assumption.
        apply diff_neg_32. assumption. assumption.
      rewrite load_store_diff.
        apply diff_0. assumption.
        apply diff_neg_0. assumption. assumption.
      rewrite load_store_diff.
        apply uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64)). by progress. assumption.
        apply uint256_le_sub_add_32. assumption.
      rewrite H10. by progress.
      rewrite load_store_diff.
        rewrite uint256_distrib_sub. rewrite uint256_sub_sub_cancel. rewrite W256.of_intN'. by progress.
        rewrite uint256_add_sub_cancel. by progress.
      rewrite load_store_same. rewrite W256.of_uintK pmod_small. progress. rewrite -Constants.q_eq_fieldq_p /Constants.Q in H6. smt ().
        reflexivity.
      rewrite load_store_same. rewrite W256.of_uintK pmod_small. progress. rewrite -Constants.q_eq_fieldq_p /Constants.Q in H8. smt ().
        reflexivity.
      by rewrite -Constants.q_eq_fieldq_p; assumption.
      by rewrite -Constants.q_eq_fieldq_p; assumption.
      case H39. by progress. progress. smt ().
      case H39. by progress. by progress.
      case H39. by progress. progress.
      exists (ret_factor{2}). exists p. progress.
      rewrite /addAssignPermutation_memory_footprint /pointSubAssign_memory_footprint. simplify.
      exists x640. exists x64. exists x96. exists buffer_point{2}.
      rewrite (store_store_swap_diff _ _ W256.zero).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ _ W256.zero).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ _ W256.zero). by progress. by progress.
      rewrite (store_store_swap_diff _ _ W256.zero). by progress. by progress.
      rewrite store_store_same.              
      rewrite (store_store_swap_diff _ _ (W256.of_int 32)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ _ (W256.of_int 32)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ _ (W256.of_int 32)). by progress. by progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ (W256.of_int 64)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ _ (W256.of_int 64)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ W256.zero).
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (store_store_swap_diff _ _ W256.zero).
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (store_store_swap_diff _ _ W256.zero).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ _ W256.zero).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ _ W256.zero). by progress. by progress.
      rewrite (store_store_swap_diff _ _ W256.zero). by progress. by progress.
      rewrite store_store_same.              
      rewrite (store_store_swap_diff _ (QUERIES_BUFFER_POINT_SLOT + (W256.of_int 32)) (W256.of_int 32)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_BUFFER_POINT_SLOT (W256.of_int 32)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ (W256.of_int 64) (W256.of_int 32)). by progress. by progress.
      rewrite store_store_same.
      pose load1 := load _ _.
      pose load2 := load _ _.
      pose load3 := load _ _.
      pose load4 := load _ _.
      rewrite (store_store_swap_diff _ _ W256.zero).
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      have ->: load1 = load3.
        rewrite /load1 /load3.
        rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. assumption.
          rewrite uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64)). by progress. assumption.
        rewrite load_store_diff.
          apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
          apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
        rewrite load_store_diff.
          apply diff_64. apply uint256_le_of_le. by progress.
          apply diff_neg_64. apply uint256_le_of_le. by progress. apply uint256_le_of_le. simplify. apply (le_trans _ 64). by progress. assumption.
        rewrite load_store_diff.
          apply diff_32. apply uint256_le_of_le. by progress.
          apply diff_neg_32. apply uint256_le_of_le. by progress. apply uint256_le_of_le. simplify. apply (le_trans _ 64). by progress. assumption.
        rewrite load_store_diff.
          assumption.
          apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
        rewrite load_store_diff.
          apply diff_0. apply uint256_le_of_le. by progress.
          apply diff_neg_0. apply uint256_le_of_le. by progress. apply uint256_le_of_le. simplify. apply (le_trans _ 64). by progress. assumption.
        rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. assumption.
          rewrite uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64)). by progress. assumption.
        rewrite load_store_diff.
          apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
          apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
        rewrite load_store_diff.
          apply diff_64. apply uint256_le_of_le. by progress.
          apply diff_neg_64. apply uint256_le_of_le. by progress. apply uint256_le_of_le. simplify. apply (le_trans _ 64). by progress. assumption.
        rewrite load_store_diff.
          apply diff_32. apply uint256_le_of_le. by progress.
          apply diff_neg_32. apply uint256_le_of_le. by progress. apply uint256_le_of_le. simplify. apply (le_trans _ 64). by progress. assumption.
        rewrite load_store_diff.
          apply diff_0. apply uint256_le_of_le. by progress.
          apply diff_neg_0. apply uint256_le_of_le. by progress. apply uint256_le_of_le. simplify. apply (le_trans _ 64). by progress. assumption.
        rewrite load_store_diff.
          assumption.
          apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
        reflexivity.
      rewrite (store_store_swap_diff _ (QUERIES_BUFFER_POINT_SLOT + (W256.of_int 32)) (W256.of_int 64)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_BUFFER_POINT_SLOT (W256.of_int 64)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite store_store_same.
      have ->: load2 = load4.
        rewrite /load2 /load4.
        rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. assumption.
          rewrite uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64)). by progress. assumption.
        rewrite load_store_diff.
          apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
          rewrite uint256_le_sub_add_32. assumption.
        rewrite load_store_diff.
          apply diff_64. assumption.
          apply diff_neg_64. assumption. assumption.
        rewrite load_store_diff.
          apply (uint256_le_le_trans _ (W256.of_int 128)). smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite uint256_distrib_sub. apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. progress. smt (@W256 @Utils).
        rewrite load_store_diff.
          rewrite uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64)). by progress. assumption.
          rewrite uint256_le_sub_add_32. assumption.
        rewrite load_store_diff.
          apply diff_0. assumption.
          apply diff_neg_0. assumption. assumption. 
        rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. assumption.
          rewrite uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64)). by progress. assumption.
        rewrite load_store_diff.
          apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. assumption.
          rewrite uint256_le_sub_add_32. assumption.
        rewrite load_store_diff.
          apply diff_64. assumption.
          apply diff_neg_64. assumption. assumption.
        rewrite load_store_diff.
          apply (uint256_le_le_trans _ (W256.of_int 128)). smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite uint256_distrib_sub. apply (uint256_le_le_trans _ (W256.of_int 64)). by progress. progress. smt (@W256 @Utils).
        rewrite load_store_diff.
          rewrite diff_0. assumption.
          rewrite diff_neg_0. assumption. assumption.
        rewrite load_store_diff.
          rewrite uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64)). by progress. assumption.
          rewrite uint256_le_sub_add_32. assumption.
        reflexivity.
      reflexivity.
    qed.

lemma addAssignPermutationLinearisationContributionWithV_mid_equiv_high_encapsulated:
    equiv [
      AddAssignPermutationLinearisationContributionWithV.mid ~ AddAssignPermutationLinearisationContributionWithV.high_encapsulated:
      point{1} = F_to_int_point(aspoint_G1 point{2}) /\
      vk_permutation_3{1} = F_to_int_point(aspoint_G1 vk_permutation_3{2}) /\
      stateOpening0AtZ{1} = FieldR.asint stateOpening0AtZ{2} /\
      stateOpening1AtZ{1} = FieldR.asint stateOpening1AtZ{2} /\
      stateOpening2AtZ{1} = FieldR.asint stateOpening2AtZ{2} /\
      stateOpening3AtZ{1} = FieldR.asint stateOpening3AtZ{2} /\
      state_beta{1} = FieldR.asint state_beta{2} /\
      state_v{1} = FieldR.asint state_v{2} /\
      state_z{1} = FieldR.asint state_z{2} /\
      state_gamma{1} = FieldR.asint state_gamma{2} /\
      state_alpha4{1} = FieldR.asint state_alpha4{2} /\
      state_alpha5{1} = FieldR.asint state_alpha5{2} /\
      state_gp_omega{1} = FieldR.asint state_gp_omega{2} /\
      state_l0AtZ{1} = FieldR.asint state_l0AtZ{2} /\
      poly0_opening{1} = FieldR.asint poly0_opening{2} /\
      poly1_opening{1} = FieldR.asint poly1_opening{2} /\
      poly2_opening{1} = FieldR.asint poly2_opening{2} ==>
      res{1} = Some (FieldR.asint res{2}.`1, F_to_int_point(aspoint_G1 res{2}.`2))
    ].
    proof.
      proc.
      seq 18 1: (
        #pre /\
        ret_factor{1} = FieldR.asint ret_factor{2}
      ).
      wp. skip. progress.
      rewrite FieldR.mulE Constants.r_eq_fieldr_p. congr. congr. congr.
      rewrite FieldR.addE. congr. congr. congr; first last.
        rewrite FieldR.mulE. reflexivity.
      rewrite FieldR.mulE. congr. congr. congr; first last.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.mulE. congr. congr. congr.
        rewrite FieldR.mulE. reflexivity.
        rewrite FieldR.inFK /Constants.NON_RESIDUE_2 pmod_small. rewrite -Constants.r_eq_fieldr_p /Constants.R. by progress. by progress.
      rewrite FieldR.mulE. congr. congr. congr; first last.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.mulE. congr. congr. congr.
        rewrite FieldR.mulE. reflexivity.
        rewrite FieldR.inFK /Constants.NON_RESIDUE_1 pmod_small. rewrite -Constants.r_eq_fieldr_p /Constants.R. by progress. by progress.
      rewrite FieldR.mulE. congr. congr. congr; first last.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.mulE. congr. congr. congr.
        rewrite FieldR.mulE. reflexivity.
        rewrite FieldR.inFK /Constants.NON_RESIDUE_0 pmod_small. rewrite -Constants.r_eq_fieldr_p /Constants.R. by progress. by progress.
      rewrite FieldR.mulE. congr. congr. congr; first last.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.mulE. reflexivity.
      sp.
      seq 3 1: (
        #pre /\
        !failed{1} /\
        buffer_point{1} = F_to_int_point(aspoint_G1 buffer_point{2})
      ).
      wp.
      call pointMulIntoDest_mid_equiv_high.
      skip. progress.
      rewrite Constants.r_eq_fieldr_p.
      rewrite FieldR.mulE. congr. congr. congr.
      rewrite FieldR.mulE. congr. congr. congr; first last.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.mulE. reflexivity.
      rewrite FieldR.mulE. congr. congr. congr; first last.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.mulE. reflexivity.
      rewrite FieldR.mulE. congr. congr. congr; first last.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.addE. congr. congr. congr.
        rewrite FieldR.mulE. reflexivity.
      rewrite FieldR.mulE. congr. congr. congr; first last.
      rewrite FieldR.mulE. reflexivity.
      
      seq 1 1: (
        #pre /\
        ret_point{1} = Some(F_to_int_point(aspoint_G1 ret_point{2}))
      ).
      call pointSubAssign_mid_equiv_high.
      skip. progress.
      wp. skip. by progress.
qed.

lemma addAssignPermutationLinearisationContributionWithV_mid_equiv_high:
    equiv [
      AddAssignPermutationLinearisationContributionWithV.mid ~ AddAssignPermutationLinearisationContributionWithV.high:
      point{1} = F_to_int_point(aspoint_G1 point{2}) /\
      vk_permutation_3{1} = F_to_int_point(aspoint_G1 vk_permutation_3{2}) /\
      stateOpening0AtZ{1} = FieldR.asint stateOpening0AtZ{2} /\
      stateOpening1AtZ{1} = FieldR.asint stateOpening1AtZ{2} /\
      stateOpening2AtZ{1} = FieldR.asint stateOpening2AtZ{2} /\
      stateOpening3AtZ{1} = FieldR.asint stateOpening3AtZ{2} /\
      state_beta{1} = FieldR.asint state_beta{2} /\
      state_v{1} = FieldR.asint state_v{2} /\
      state_z{1} = FieldR.asint state_z{2} /\
      state_gamma{1} = FieldR.asint state_gamma{2} /\
      state_alpha4{1} = FieldR.asint state_alpha4{2} /\
      state_alpha5{1} = FieldR.asint state_alpha5{2} /\
      state_gp_omega{1} = FieldR.asint state_gp_omega{2} /\
      state_l0AtZ{1} = FieldR.asint state_l0AtZ{2} /\
      poly0_opening{1} = FieldR.asint poly0_opening{2} /\
      poly1_opening{1} = FieldR.asint poly1_opening{2} /\
      poly2_opening{1} = FieldR.asint poly2_opening{2} ==>
      res{1} = Some (FieldR.asint res{2}.`1, F_to_int_point(aspoint_G1 res{2}.`2))
    ].
    proof.
    transitivity AddAssignPermutationLinearisationContributionWithV.high_encapsulated
    (
      point{1} = F_to_int_point(aspoint_G1 point{2}) /\
      vk_permutation_3{1} = F_to_int_point(aspoint_G1 vk_permutation_3{2}) /\
      stateOpening0AtZ{1} = FieldR.asint stateOpening0AtZ{2} /\
      stateOpening1AtZ{1} = FieldR.asint stateOpening1AtZ{2} /\
      stateOpening2AtZ{1} = FieldR.asint stateOpening2AtZ{2} /\
      stateOpening3AtZ{1} = FieldR.asint stateOpening3AtZ{2} /\
      state_beta{1} = FieldR.asint state_beta{2} /\
      state_v{1} = FieldR.asint state_v{2} /\
      state_z{1} = FieldR.asint state_z{2} /\
      state_gamma{1} = FieldR.asint state_gamma{2} /\
      state_alpha4{1} = FieldR.asint state_alpha4{2} /\
      state_alpha5{1} = FieldR.asint state_alpha5{2} /\
      state_gp_omega{1} = FieldR.asint state_gp_omega{2} /\
      state_l0AtZ{1} = FieldR.asint state_l0AtZ{2} /\
      poly0_opening{1} = FieldR.asint poly0_opening{2} /\
      poly1_opening{1} = FieldR.asint poly1_opening{2} /\
      poly2_opening{1} = FieldR.asint poly2_opening{2} ==>
      res{1} = Some (FieldR.asint res{2}.`1, F_to_int_point(aspoint_G1 res{2}.`2))
    )
    (
      ={arg} ==> ={res}
    ).
    progress. exists (arg{2}). by progress.
    progress. exact addAssignPermutationLinearisationContributionWithV_mid_equiv_high_encapsulated.
    proc.
      inline*. wp. skip. by progress.
qed.









