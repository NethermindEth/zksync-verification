pragma Goals:printall.

require import AllCore.
require        Constants.
require import Field.
require import PointAddAssign.
require import PointMulAndAddIntoDest.
require import PointMulIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

module AddAssignRescueCustomGateLinearisationContributionWithV = {
  proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256, stateOpening3AtZ : uint256): unit = {
    var accumulator, intermediateValue, _4, _7, _10, _12;
    accumulator <- (PurePrimops.mulmod stateOpening0AtZ stateOpening0AtZ R_MOD);
    accumulator <- (PurePrimops.addmod accumulator (R_MOD - stateOpening1AtZ) R_MOD);
    _4 <@ Primops.mload(STATE_ALPHA_SLOT);
    accumulator <- (PurePrimops.mulmod accumulator _4 R_MOD);
    intermediateValue <- (PurePrimops.mulmod stateOpening1AtZ stateOpening1AtZ R_MOD);
    intermediateValue <- (PurePrimops.addmod intermediateValue (R_MOD - stateOpening2AtZ) R_MOD);
    _7 <@ Primops.mload(STATE_POWER_OF_ALPHA_2_SLOT);
    intermediateValue <- (PurePrimops.mulmod intermediateValue _7 R_MOD);
    accumulator <- (PurePrimops.addmod accumulator intermediateValue R_MOD);
    intermediateValue <- (PurePrimops.mulmod stateOpening2AtZ stateOpening0AtZ R_MOD);
    intermediateValue <- (PurePrimops.addmod intermediateValue (R_MOD - stateOpening3AtZ) R_MOD);
    _10 <@ Primops.mload(STATE_POWER_OF_ALPHA_3_SLOT);
    intermediateValue <- (PurePrimops.mulmod intermediateValue _10 R_MOD);
    accumulator <- (PurePrimops.addmod accumulator intermediateValue R_MOD);
    _12 <@ Primops.mload(STATE_V_SLOT);
    accumulator <- (PurePrimops.mulmod accumulator _12 R_MOD);
    PointMulAndAddIntoDest.low(VK_GATE_SELECTORS_1_X_SLOT, accumulator, dest);
  }

  proc mid(point: (int*int), stateOpening0AtZ: int, stateOpening1AtZ: int, stateOpening2AtZ: int, stateOpening3AtZ: int, state_alpha: int, state_alpha2: int, state_alpha3: int, state_v: int, vk_gate_selector_1: (int*int)): (int*int) option = {
    var n, ret;
    n <- ((
      ((stateOpening0AtZ * stateOpening0AtZ - stateOpening1AtZ) * state_alpha) +
      ((stateOpening1AtZ * stateOpening1AtZ - stateOpening2AtZ) * state_alpha2) +
      ((stateOpening2AtZ * stateOpening0AtZ - stateOpening3AtZ) * state_alpha3)
    ) * state_v) %% Constants.R;
    ret <@ PointMulAndAddIntoDest.mid(vk_gate_selector_1.`1, vk_gate_selector_1.`2, n, point.`1, point.`2);
    return ret;
  }

  proc high_encapsulated(point: g, stateOpening0AtZ: FieldR.F, stateOpening1AtZ: FieldR.F, stateOpening2AtZ: FieldR.F, stateOpening3AtZ: FieldR.F, state_alpha: FieldR.F, state_alpha2: FieldR.F, state_alpha3: FieldR.F, state_v: FieldR.F, vk_gate_selector_1: g): g = {
    var n, ret;
    n <- (
      ((stateOpening0AtZ * stateOpening0AtZ - stateOpening1AtZ) * state_alpha) +
      ((stateOpening1AtZ * stateOpening1AtZ - stateOpening2AtZ) * state_alpha2) +
      ((stateOpening2AtZ * stateOpening0AtZ - stateOpening3AtZ) * state_alpha3)
    ) * state_v;
    ret <@ PointMulAndAddIntoDest.high(vk_gate_selector_1, n, point);
    return ret;
  }

  proc high(point: g, stateOpening0AtZ: FieldR.F, stateOpening1AtZ: FieldR.F, stateOpening2AtZ: FieldR.F, stateOpening3AtZ: FieldR.F, state_alpha: FieldR.F, state_alpha2: FieldR.F, state_alpha3: FieldR.F, state_v: FieldR.F, vk_gate_selector_1: g): g = {
    return (((
      ((stateOpening0AtZ * stateOpening0AtZ - stateOpening1AtZ) * state_alpha) +
      ((stateOpening1AtZ * stateOpening1AtZ - stateOpening2AtZ) * state_alpha2) +
      ((stateOpening2AtZ * stateOpening0AtZ - stateOpening3AtZ) * state_alpha3)
    ) * state_v) * vk_gate_selector_1) + point;
  }
}.

lemma addAssignRescueCustomGateLinearisationContributionWithV_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_addAssignRescueCustomGateLinearisationContributionWithV ~ AddAssignRescueCustomGateLinearisationContributionWithV.low :
      ={arg, glob AddAssignRescueCustomGateLinearisationContributionWithV} ==>
      ={res, glob AddAssignRescueCustomGateLinearisationContributionWithV}
    ].
proof.
  proc.
  call (pointMulAndAddIntoDest_extracted_equiv_low).
  inline*. wp. skip. rewrite /Constants.R. by progress.
qed.

lemma addAssignRescueCustomGateLinearisationContributionWithV_low_pspec_revert :
    phoare [
      AddAssignRescueCustomGateLinearisationContributionWithV.low:
      Primops.reverted ==>
      Primops.reverted
    ] = 1%r.
    proof.
      proc.
      call pointMulAndAddIntoDest_low_pspec_revert.
      inline*. wp. skip. by progress.
qed.

op addAssignRescue_memory_footprint (mem_0: mem) (dest: uint256) (ret: (int*int)) (scratch1 scratch2 scratch3 scratch4: uint256): mem =
    let mem_1 = store mem_0 W256.zero scratch1 in
    let mem_2 = store mem_1 (W256.of_int 32) scratch2 in
    let mem_3 = store mem_2 (W256.of_int 64) scratch3 in
    let mem_4 = store mem_3 (W256.of_int 96) scratch4 in
    let mem_5 = store mem_4 dest (W256.of_int ret.`1) in
    store mem_5 (dest + W256.of_int 32) (W256.of_int ret.`2).

lemma addAssignRescueCustomGateLinearisationContributionWithV_low_equiv_mid
    (mem_0: mem)
    (low_dest low_stateOpening0AtZ low_stateOpening1AtZ low_stateOpening2AtZ low_stateOpening3AtZ : uint256)
    (mid_stateOpening0AtZ, mid_stateOpening1AtZ, mid_stateOpening2AtZ, mid_stateOpening3AtZ, mid_state_alpha, mid_state_alpha2, mid_state_alpha3, mid_state_v: int)
    (mid_point, mid_vk_gate_selector_1: (int*int)):
equiv [
    AddAssignRescueCustomGateLinearisationContributionWithV.low ~ AddAssignRescueCustomGateLinearisationContributionWithV.mid :
      arg{1} = (low_dest, low_stateOpening0AtZ, low_stateOpening1AtZ, low_stateOpening2AtZ, low_stateOpening3AtZ) /\
      arg{2} = (mid_point, mid_stateOpening0AtZ, mid_stateOpening1AtZ, mid_stateOpening2AtZ, mid_stateOpening3AtZ, mid_state_alpha, mid_state_alpha2, mid_state_alpha3, mid_state_v, mid_vk_gate_selector_1) /\
      W256.to_uint low_stateOpening0AtZ = mid_stateOpening0AtZ /\
      W256.to_uint low_stateOpening1AtZ = mid_stateOpening1AtZ /\
      W256.to_uint low_stateOpening2AtZ = mid_stateOpening2AtZ /\
      W256.to_uint low_stateOpening3AtZ = mid_stateOpening3AtZ /\
      0 <= mid_stateOpening0AtZ < Constants.R /\
      0 <= mid_stateOpening1AtZ < Constants.R /\
      0 <= mid_stateOpening2AtZ < Constants.R /\
      0 <= mid_stateOpening3AtZ < Constants.R /\
      0 <= mid_point.`1 < Constants.Q /\
      0 <= mid_point.`2 < Constants.Q /\
      0 <= mid_vk_gate_selector_1.`1 < Constants.Q /\
      0 <= mid_vk_gate_selector_1.`2 < Constants.Q /\
      W256.of_int 128 <= low_dest /\
      W256.of_int 64 <= - low_dest /\
      W256.to_uint (load mem_0 low_dest) = mid_point.`1 /\
      W256.to_uint (load mem_0 (low_dest + W256.of_int 32)) = mid_point.`2 /\
      W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_X_SLOT) = mid_vk_gate_selector_1.`1 /\
      W256.to_uint (load mem_0 (VK_GATE_SELECTORS_1_X_SLOT + W256.of_int 32)) = mid_vk_gate_selector_1.`2 /\
      W256.to_uint (load mem_0 STATE_V_SLOT) = mid_state_v /\
      W256.to_uint (load mem_0 STATE_ALPHA_SLOT) = mid_state_alpha /\
      W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_2_SLOT) = mid_state_alpha2 /\
      W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_3_SLOT) = mid_state_alpha3 /\
      !Primops.reverted{1} /\
      Primops.memory{1} = mem_0 ==>
      (
        (!Primops.reverted{1} /\ exists (p: (int*int)) (scratch1 scratch2 scratch3 scratch4: uint256), (
          Primops.memory{1} = addAssignRescue_memory_footprint mem_0 low_dest p scratch1 scratch2 scratch3 scratch4 /\
          res{2} = Some p /\
          0 <= p.`1 < Constants.Q /\
          0 <= p.`2 < Constants.Q
        ))  \/
        (Primops.reverted{1} /\ res{2} = None)
      )
    ].
    proof.
      proc.
      pose mid_n := ((
        ((mid_stateOpening0AtZ * mid_stateOpening0AtZ - mid_stateOpening1AtZ) * mid_state_alpha) +
        ((mid_stateOpening1AtZ * mid_stateOpening1AtZ - mid_stateOpening2AtZ) * mid_state_alpha2) +
        ((mid_stateOpening2AtZ * mid_stateOpening0AtZ - mid_stateOpening3AtZ) * mid_state_alpha3)
      ) * mid_state_v) %% Constants.R.
      call (
      pointMulAndAddIntoDest_low_equiv_mid
      (W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_X_SLOT))
      (W256.to_uint (load mem_0 (VK_GATE_SELECTORS_1_X_SLOT + W256.of_int 32)))
      mid_point.`1
      mid_point.`2
      mid_n
      VK_GATE_SELECTORS_1_X_SLOT
      low_dest
      mem_0
      ).
          inline Primops.mload.
          wp.
          skip.
          rewrite Constants.q_eq_fieldq_p.
          progress.
          smt ().
          smt ().
          smt ().
          smt ().
          smt ().
          smt ().
          rewrite /VerifierConsts.VK_GATE_SELECTORS_1_X_SLOT. smt (@W256 @Utils).
          rewrite /VerifierConsts.VK_GATE_SELECTORS_1_X_SLOT. smt (@W256 @Utils).
          smt (@W256 @Utils).
          smt (@W256 @Utils).
          smt (@W256).
          smt (@W256).
          rewrite /mid_n. 
          rewrite /mulmod /addmod. progress. congr.
          do rewrite W256.of_uintK.
          do 12! (rewrite (pmod_small _ W256.modulus); first smt (@IntDiv @W256)).
          rewrite - /Constants.R.
          pose o0 := to_uint stateOpening0AtZ{1}.
          pose o1 := to_uint stateOpening1AtZ{1}.
          pose o2 := to_uint stateOpening2AtZ{1}.
          pose o3 := to_uint stateOpening3AtZ{1}.
          pose a := to_uint (load Primops.memory{1} STATE_ALPHA_SLOT).
          pose a2 := to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_2_SLOT).
          pose v := to_uint (load Primops.memory{1} STATE_V_SLOT).
          pose a3 := to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_3_SLOT).
          have H_add: forall (a b c: int),  (a %% b + c) %% b = (a + c) %% b by smt(@IntDiv).
          do rewrite H_add.
          do rewrite Utils.uint256_cast_sub. do rewrite W256.of_uintK. rewrite - /Constants.R.
          (* PICKUP HERE *)
          have H_mul: forall(a b c: int), (a %% b * c) %% b = (a * c) %% b by smt (@IntDiv).
          do rewrite H_mul.
          do 6! (rewrite (pmod_small _ W256.modulus); first smt (@IntDiv @W256)).
          rewrite - /o1. rewrite - /o2. rewrite - /o3. smt (@IntDiv).
          smt ().
          smt ().
          case H47; first last. by progress.
          progress. case H48; first last. by progress.
          progress.
          rewrite /addAssignRescue_memory_footprint.
          exists (F_to_int_point (x', y')).
          exists (W256.of_int (FieldQ.asint x)).
          exists (W256.of_int (FieldQ.asint y)).
          exists (W256.of_int point{2}.`1).
          exists (W256.of_int point{2}.`2).
          progress.
          exact F_to_int_point_1_ge_zero.
          exact F_to_int_point_1_lt_p.
          exact F_to_int_point_2_ge_zero.
          exact F_to_int_point_2_lt_p.          
      qed.

lemma addAssignRescueCustomGateLinearisationContributionWithV_mid_equiv_high:
    equiv [
      AddAssignRescueCustomGateLinearisationContributionWithV.mid ~ AddAssignRescueCustomGateLinearisationContributionWithV.high :
      point{1} = F_to_int_point(aspoint_G1 point{2}) /\
      vk_gate_selector_1{1} = F_to_int_point(aspoint_G1 vk_gate_selector_1{2}) /\
      stateOpening0AtZ{1} = FieldR.asint stateOpening0AtZ{2} /\
      stateOpening1AtZ{1} = FieldR.asint stateOpening1AtZ{2} /\
      stateOpening2AtZ{1} = FieldR.asint stateOpening2AtZ{2} /\
      stateOpening3AtZ{1} = FieldR.asint stateOpening3AtZ{2} /\
      state_alpha{1} = FieldR.asint state_alpha{2} /\
      state_alpha2{1} = FieldR.asint state_alpha2{2} /\
      state_alpha3{1} = FieldR.asint state_alpha3{2} /\
      state_v{1} = FieldR.asint state_v{2} ==>
      res{1} = Some (F_to_int_point(aspoint_G1 res{2}))
    ].
    proof.
      transitivity AddAssignRescueCustomGateLinearisationContributionWithV.high_encapsulated
      (
        point{1} = F_to_int_point(aspoint_G1 point{2}) /\
        vk_gate_selector_1{1} = F_to_int_point(aspoint_G1 vk_gate_selector_1{2}) /\
        stateOpening0AtZ{1} = FieldR.asint stateOpening0AtZ{2} /\
        stateOpening1AtZ{1} = FieldR.asint stateOpening1AtZ{2} /\
        stateOpening2AtZ{1} = FieldR.asint stateOpening2AtZ{2} /\
        stateOpening3AtZ{1} = FieldR.asint stateOpening3AtZ{2} /\
        state_alpha{1} = FieldR.asint state_alpha{2} /\
        state_alpha2{1} = FieldR.asint state_alpha2{2} /\
        state_alpha3{1} = FieldR.asint state_alpha3{2} /\
        state_v{1} = FieldR.asint state_v{2} ==>
        res{1} = Some (F_to_int_point(aspoint_G1 res{2}))
      )
      (
        ={arg} ==> ={res}
      ).
      progress. exists arg{2}. by progress.
      by progress.
      proc.
      sp.
      call pointMulAndAddIntoDest_mid_equiv_high.
      skip.
      progress.
      rewrite FieldR.mulE.
      rewrite -modzMm.
      congr. congr; first last. exact Constants.r_eq_fieldr_p. congr; first last.
      rewrite pmod_small. progress. exact FieldR.ge0_asint. rewrite Constants.r_eq_fieldr_p. exact FieldR.gtp_asint. reflexivity.
      rewrite FieldR.addE.
      rewrite -modzDm.
      congr. congr; first last. exact Constants.r_eq_fieldr_p. congr; first last.
      rewrite FieldR.mulE.
      rewrite -modzMm.
      congr. congr; first last. exact Constants.r_eq_fieldr_p. congr; first last.
      rewrite pmod_small. progress. exact FieldR.ge0_asint. rewrite Constants.r_eq_fieldr_p. exact FieldR.gtp_asint. reflexivity.
      rewrite FieldR.addE.
      rewrite -modzDm.
      congr. congr; first last. exact Constants.r_eq_fieldr_p. congr; first last.
      rewrite FieldR.oppE Constants.r_eq_fieldr_p. reflexivity.
      rewrite FieldR.mulE Constants.r_eq_fieldr_p. reflexivity.
      rewrite FieldR.addE.
      rewrite -modzDm.
      congr. congr; first last. exact Constants.r_eq_fieldr_p. congr; first last.
      rewrite FieldR.mulE.
      rewrite -modzMm.
      congr. congr; first last. exact Constants.r_eq_fieldr_p. congr; first last.
      rewrite pmod_small. progress. exact FieldR.ge0_asint. rewrite Constants.r_eq_fieldr_p. exact FieldR.gtp_asint. reflexivity.
      rewrite FieldR.addE.
      rewrite -modzDm.
      congr. congr; first last. exact Constants.r_eq_fieldr_p. congr; first last.
      rewrite FieldR.oppE Constants.r_eq_fieldr_p. reflexivity.
      rewrite FieldR.mulE Constants.r_eq_fieldr_p. reflexivity.
      rewrite FieldR.mulE.
      rewrite -modzMm.
      congr. congr; first last. exact Constants.r_eq_fieldr_p. congr; first last.
      rewrite pmod_small. progress. exact FieldR.ge0_asint. rewrite Constants.r_eq_fieldr_p. exact FieldR.gtp_asint. reflexivity.
      rewrite FieldR.addE.
      rewrite -modzDm.
      congr. congr; first last. exact Constants.r_eq_fieldr_p. congr; first last.
      rewrite FieldR.oppE Constants.r_eq_fieldr_p. reflexivity.
      rewrite FieldR.mulE Constants.r_eq_fieldr_p. reflexivity.
      
      proc.
      inline*. wp. skip. by progress.
qed.



















