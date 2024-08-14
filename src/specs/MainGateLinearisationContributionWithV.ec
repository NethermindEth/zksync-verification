pragma Goals: printall.

require        Constants.
require import PointAddAssign.
require import PointAddIntoDest.
require import PointMulAndAddIntoDest.
require import PointMulIntoDest.
require import PurePrimops.
require import UInt256.
require import Utils.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

module MainGateLinearisationContributionWithV = {
  proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256, stateOpening3AtZ : uint256): unit = {
  var _6, _8, _12, _15, _17, coeff;
    PointMulIntoDest.low(VK_GATE_SETUP_0_X_SLOT, stateOpening0AtZ, dest);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_1_X_SLOT, stateOpening1AtZ, dest);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_2_X_SLOT, stateOpening2AtZ, dest);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_3_X_SLOT, stateOpening3AtZ, dest);
    _6 <- (PurePrimops.mulmod stateOpening0AtZ stateOpening1AtZ R_MOD);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_4_X_SLOT, _6, dest);
    _8 <- (PurePrimops.mulmod stateOpening0AtZ stateOpening2AtZ R_MOD);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_5_X_SLOT, _8, dest);
    PointAddAssign.low(dest, VK_GATE_SETUP_6_X_SLOT);
    _12 <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_7_X_SLOT, _12, dest);
    _15 <@ Primops.mload(STATE_V_SLOT);
    _17 <@ Primops.mload(PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT);
    coeff <- (PurePrimops.mulmod _17 _15 R_MOD);
    PointMulIntoDest.low(dest, coeff, dest);
  }

  proc mid(vk_gate_setup_0: int*int, vk_gate_setup_1: int*int, vk_gate_setup_2: int*int, vk_gate_setup_3: int*int, vk_gate_setup_4: int*int, vk_gate_setup_5: int*int, vk_gate_setup_6: int*int, vk_gate_setup_7: int*int, stateOpening0AtZ: int, stateOpening1AtZ: int, stateOpening2AtZ: int, stateOpening3AtZ: int, poly3_omega: int, v: int, gate_selector_0_opening: int): (int*int) option = {
      var point_opt: (int*int) option;
      var point: int*int;
      var factor_4, factor_5, factor_7, final_factor: int;
      var failed: bool;
    
      failed <- false;
      point_opt <@ PointMulIntoDest.mid(vk_gate_setup_0.`1, vk_gate_setup_0.`2, stateOpening0AtZ);
      failed <- failed \/ is_none point_opt;
      point <- odflt (0,0) point_opt;
    
      point_opt <@ PointMulAndAddIntoDest.mid(vk_gate_setup_1.`1, vk_gate_setup_1.`2, stateOpening1AtZ, point.`1, point.`2);
      failed <- failed \/ is_none point_opt;
      point <- odflt (0,0) point_opt;
    
      point_opt <@ PointMulAndAddIntoDest.mid(vk_gate_setup_2.`1, vk_gate_setup_2.`2, stateOpening2AtZ, point.`1, point.`2);
      failed <- failed \/ is_none point_opt;
      point <- odflt (0,0) point_opt;
    
      point_opt <@ PointMulAndAddIntoDest.mid(vk_gate_setup_3.`1, vk_gate_setup_3.`2, stateOpening3AtZ, point.`1, point.`2);
      failed <- failed \/ is_none point_opt;
      point <- odflt (0,0) point_opt;
    
      factor_4 <- (stateOpening0AtZ * stateOpening1AtZ) %% Constants.R;
      point_opt <@ PointMulAndAddIntoDest.mid(vk_gate_setup_4.`1, vk_gate_setup_4.`2, factor_4, point.`1, point.`2);
      failed <- failed \/ is_none point_opt;
      point <- odflt (0,0) point_opt;
    
      factor_5 <- (stateOpening0AtZ * stateOpening2AtZ) %% Constants.R;
      point_opt <@ PointMulAndAddIntoDest.mid(vk_gate_setup_5.`1, vk_gate_setup_5.`2, factor_5, point.`1, point.`2);
      failed <- failed \/ is_none point_opt;
      point <- odflt (0,0) point_opt;
    
      point_opt <@ PointAddIntoDest.mid(point.`1, point.`2, vk_gate_setup_6.`1, vk_gate_setup_6.`2);
      failed <- failed \/ is_none point_opt;
      point <- odflt (0,0) point_opt;
    
      point_opt <@ PointMulAndAddIntoDest.mid(vk_gate_setup_7.`1, vk_gate_setup_7.`2, poly3_omega, point.`1, point.`2);
      failed <- failed \/ is_none point_opt;
      point <- odflt (0,0) point_opt;
    
      final_factor <- v * gate_selector_0_opening %% Constants.R;
      point_opt <@ PointMulIntoDest.mid(point.`1, point.`2, final_factor);
      if (failed) {
        point_opt <- None;
      }
      return point_opt;
  }
}.

lemma mainGateLinearisationContributionWithV_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_mainGateLinearisationContributionWithV ~ MainGateLinearisationContributionWithV.low :
      ={arg, glob MainGateLinearisationContributionWithV} ==>
      ={res, glob MainGateLinearisationContributionWithV}
    ].
proof.
  proc.
  inline Primops.mload.
  call (pointMulIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointAddAssign_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulIntoDest_extracted_equiv_low). wp.
  skip. rewrite /Constants.R. by progress.
qed.

prover timeout=100.

lemma vk_gate_setup_separation_1 (x y: uint256):
    W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - x =>
    VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= x - VK_GATE_SETUP_0_X_SLOT =>
    VK_GATE_SETUP_0_X_SLOT <= y <= VK_GATE_SETUP_7_Y_SLOT =>
    W256.of_int 32 <= y - x.
    proof.
      rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT. simplify.
      progress.
      smt (@W256 @Utils).
  qed.

lemma vk_gate_setup_separation_2 (x y: uint256):
    W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - x =>
    VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= x - VK_GATE_SETUP_0_X_SLOT =>
    VK_GATE_SETUP_0_X_SLOT <= y <= VK_GATE_SETUP_7_Y_SLOT =>
    W256.of_int 32 <= x - y.
    proof.
      rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT. simplify.
      progress.
      smt (@W256 @Utils).
  qed.

lemma vk_gate_setup_separation_3 (x y: uint256):
    W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - x =>
    VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= x - VK_GATE_SETUP_0_X_SLOT =>
    VK_GATE_SETUP_0_X_SLOT <= y <= VK_GATE_SETUP_7_Y_SLOT =>
    W256.of_int 32 <= y - (x + W256.of_int 32).
    proof.
      rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT. simplify.
      progress.
      smt (@W256 @Utils).
  qed.

lemma vk_gate_setup_separation_4 (x y: uint256):
    W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - x =>
    VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= x - VK_GATE_SETUP_0_X_SLOT =>
    VK_GATE_SETUP_0_X_SLOT <= y <= VK_GATE_SETUP_7_Y_SLOT =>
    W256.of_int 32 <= (x + W256.of_int 32) - y.
    proof.
      rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT. simplify.
      progress.
      smt (@W256 @Utils).
  qed.

lemma vk_gate_setup_separation_mulIntoDest (vk_gate_setup: int) (dest slot x0 x32 x64 x y: uint256) (memory: mem):
    vk_gate_setup = W256.to_uint (load memory slot) =>
    VK_GATE_SETUP_0_X_SLOT <= slot =>
    slot <= VK_GATE_SETUP_7_Y_SLOT =>
    W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest =>
    VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest - VK_GATE_SETUP_0_X_SLOT =>
    vk_gate_setup =
    W256.to_uint
    (load
      (store
        (store
          (store
            (store
              (store memory W256.zero x0)
              (W256.of_int 32) x32
            ) (W256.of_int 64) x64
          ) dest x
        ) (dest + W256.of_int 32) y
      ) slot ).
    proof.
    progress.
      rewrite load_store_diff.
      apply vk_gate_setup_separation_3; (progress; assumption).
      apply vk_gate_setup_separation_4; (progress; assumption).
      rewrite load_store_diff.
      apply vk_gate_setup_separation_1; (progress; assumption).
      apply vk_gate_setup_separation_2; (progress; assumption).
      rewrite load_store_diff.
      smt (@W256 @Utils @VerifierConsts).
      smt (@W256 @Utils @VerifierConsts).
      rewrite load_store_diff.
      smt (@W256 @Utils @VerifierConsts).
      smt (@W256 @Utils @VerifierConsts).
      rewrite load_store_diff.
      smt (@W256 @Utils @VerifierConsts).
      smt (@W256 @Utils @VerifierConsts).
      reflexivity.
  qed.

lemma vk_gate_setup_separation_mulAndAddIntoDest (vk_gate_setup: int) (dest slot x0 x32 x64 x96 x y: uint256) (memory: mem):
    vk_gate_setup = W256.to_uint (load memory slot) =>
    VK_GATE_SETUP_0_X_SLOT <= slot =>
    slot <= VK_GATE_SETUP_7_Y_SLOT =>
    W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest =>
    VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest - VK_GATE_SETUP_0_X_SLOT =>
    vk_gate_setup =
    W256.to_uint
    (load
      (store
        (store
          (store
            (store
              (store
                (store memory W256.zero x0)
                (W256.of_int 32) x32
              ) (W256.of_int 64) x64
            ) (W256.of_int 96) x96
          ) dest x
        ) (dest + W256.of_int 32) y
      ) slot ).
    proof.
    progress.
      rewrite load_store_diff.
      apply vk_gate_setup_separation_3; (progress; assumption).
      apply vk_gate_setup_separation_4; (progress; assumption).
      rewrite load_store_diff.
      apply vk_gate_setup_separation_1; (progress; assumption).
      apply vk_gate_setup_separation_2; (progress; assumption).
      rewrite load_store_diff.
      smt (@W256 @Utils @VerifierConsts).
      smt (@W256 @Utils @VerifierConsts).
      rewrite load_store_diff.
      smt (@W256 @Utils @VerifierConsts).
      smt (@W256 @Utils @VerifierConsts).
      rewrite load_store_diff.
      smt (@W256 @Utils @VerifierConsts).
      smt (@W256 @Utils @VerifierConsts).
      rewrite load_store_diff.
      smt (@W256 @Utils @VerifierConsts).
      smt (@W256 @Utils @VerifierConsts).
      reflexivity.
  qed.

lemma y_coord_in_range (x: uint256):
    W256.of_int 128 <= x =>
    W256.of_int 64 <= -x =>
    W256.of_int 128 <= (x+W256.of_int 32).
    proof.
      progress.
      smt (@W256 @Utils).
  qed.

lemma y_coord_in_range_neg (x: uint256):
    W256.of_int 128 <= x =>
    W256.of_int 64 <= -x =>
    W256.of_int 32 <= -(x + W256.of_int 32).
    proof.
      progress.
      smt (@W256 @Utils).
  qed.

lemma mulAndAddIntoDest_after_mulIntoDest (mem_0: mem) (dest: uint256) (a b: int*int) (c: int) (x0 x32 x64 x96 x y: uint256):
    W256.of_int 128 <= dest =>
    W256.of_int 64 <= -dest =>
    store(store(store(store(store(store (pointMulIntoDest_memory_footprint mem_0 dest a b c)
    W256.zero x0)
              (W256.of_int 32) x32)
            (W256.of_int 64) x64)
          (W256.of_int 96) x96)
          dest x)
    (dest + W256.of_int 32) y = 
    store(store(store(store(store(store mem_0
    W256.zero x0)
              (W256.of_int 32) x32)
            (W256.of_int 64) x64)
          (W256.of_int 96) x96)
          dest x)
    (dest + W256.of_int 32) y.
    proof.
      progress.
      rewrite /pointMulIntoDest_memory_footprint. simplify.
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ (W256.of_int 64) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 64) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ (W256.of_int 96) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 96) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ dest _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_same _ dest _ _).
      rewrite store_store_same. reflexivity.
    qed.

lemma mulAndAddIntoDest_after_mulAndAddIntoDest (mem_0: mem) (dest: uint256) (x0 x32 x64 x96 x y x0' x32' x64' x96' x' y': uint256):
    W256.of_int 128 <= dest =>
    W256.of_int 64 <= -dest =>
    store(store(store(store(store(store(store(store(store(store(store(store mem_0
    W256.zero x0')
                        (W256.of_int 32) x32')
                      (W256.of_int 64) x64')
                    (W256.of_int 96) x96')
                      dest x')
                (dest + W256.of_int 32) y')
                  W256.zero x0)
              (W256.of_int 32) x32)
            (W256.of_int 64) x64)
          (W256.of_int 96) x96)
          dest x)
    (dest + W256.of_int 32) y = 
    store(store(store(store(store(store mem_0
    W256.zero x0)
              (W256.of_int 32) x32)
            (W256.of_int 64) x64)
          (W256.of_int 96) x96)
          dest x)
    (dest + W256.of_int 32) y.
    proof.
      progress.
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_same _ W256.zero).
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_same _ (W256.of_int 32)).
      rewrite (store_store_swap_diff _ _ (W256.of_int 64) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 64) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 64) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_same _ (W256.of_int 64)).
      rewrite (store_store_swap_diff _ _ (W256.of_int 96) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 96) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_same _ (W256.of_int 96)).
      rewrite (store_store_swap_diff _ _ dest _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_same _ dest _ _).
      rewrite store_store_same. reflexivity.
    qed.

lemma mulIntoDest_after_mulAndAddIntoDest (mem_0: mem) (dest: uint256) (a b: int*int) (c: int) (x0 x32 x64 x96 x y: uint256):
    W256.of_int 128 <= dest =>
    W256.of_int 64 <= -dest =>
    pointMulIntoDest_memory_footprint (
    store(store(store(store(store(store mem_0
    W256.zero x0)
              (W256.of_int 32) x32)
            (W256.of_int 64) x64)
          (W256.of_int 96) x96)
          dest x)
    (dest + W256.of_int 32) y) dest a b c = 
    store(store(store(store(store(store mem_0
    W256.zero (W256.of_int a.`1))
              (W256.of_int 32) (W256.of_int a.`2))
            (W256.of_int 64) (W256.of_int c))
          (W256.of_int 96) x96)
          dest (W256.of_int b.`1))
    (dest + W256.of_int 32) (W256.of_int b.`2).
    proof.
      progress.
      rewrite /pointMulIntoDest_memory_footprint. simplify.
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ W256.zero _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 32) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ (W256.of_int 64) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 64) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_swap_diff _ _ (W256.of_int 64) _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ dest _ _). smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite (store_store_same _ dest _ _).
      rewrite (store_store_same _ (dest + W256.of_int 32)). reflexivity.
  qed.

op mainGateLinearisation_memory_footprint (mem_0: mem) (dest: uint256) (point result: int*int) (factor: int) (x96: uint256): mem =
    let mem_1 = store mem_0 W256.zero (W256.of_int point.`1) in
    let mem_2 = store mem_1 (W256.of_int 32) (W256.of_int point.`2) in
    let mem_3 = store mem_2 (W256.of_int 64) (W256.of_int factor) in
    let mem_4 = store mem_3 (W256.of_int 96) x96 in
    let mem_5 = store mem_4 dest (W256.of_int result.`1) in
    store mem_5 (dest + W256.of_int 32) (W256.of_int result.`2).

lemma mainGateLinearisationContributionWithV_low_equiv_mid (mem_0: mem) (dest_L: uint256):
equiv [
    MainGateLinearisationContributionWithV.low ~ MainGateLinearisationContributionWithV.mid:
    !Primops.reverted{1} /\
    Primops.memory{1} = mem_0 /\
    W256.of_int 128 <= dest{1} /\
    W256.of_int 64 <= -dest{1} /\
    W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest{1} /\
    VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest{1} - VK_GATE_SETUP_0_X_SLOT /\
    W256.of_int 64 <= PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT - dest{1} /\
    W256.of_int 32 <= dest{1} - PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /\
    W256.of_int 64 <= STATE_V_SLOT - dest{1} /\
    W256.of_int 32 <= dest{1} - STATE_V_SLOT /\
    W256.of_int 64 <= PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT - dest{1} /\
    W256.of_int 32 <= dest{1} - PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /\
    vk_gate_setup_0{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_X_SLOT) /\ vk_gate_setup_0{2}.`1 < p /\
    vk_gate_setup_0{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_Y_SLOT) /\ vk_gate_setup_0{2}.`2 < p /\
    vk_gate_setup_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_X_SLOT) /\ vk_gate_setup_1{2}.`1 < p /\
    vk_gate_setup_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_Y_SLOT) /\ vk_gate_setup_1{2}.`2 < p /\
    vk_gate_setup_2{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_X_SLOT) /\ vk_gate_setup_2{2}.`1 < p /\
    vk_gate_setup_2{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_Y_SLOT) /\ vk_gate_setup_2{2}.`2 < p /\
    vk_gate_setup_3{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_X_SLOT) /\ vk_gate_setup_3{2}.`1 < p /\
    vk_gate_setup_3{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_Y_SLOT) /\ vk_gate_setup_3{2}.`2 < p /\
    vk_gate_setup_4{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_X_SLOT) /\ vk_gate_setup_4{2}.`1 < p /\
    vk_gate_setup_4{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_Y_SLOT) /\ vk_gate_setup_4{2}.`2 < p /\
    vk_gate_setup_5{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_X_SLOT) /\ vk_gate_setup_5{2}.`1 < p /\
    vk_gate_setup_5{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_Y_SLOT) /\ vk_gate_setup_5{2}.`2 < p /\
    vk_gate_setup_6{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_X_SLOT) /\ vk_gate_setup_6{2}.`1 < p /\
    vk_gate_setup_6{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_Y_SLOT) /\ vk_gate_setup_6{2}.`2 < p /\
    vk_gate_setup_7{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_X_SLOT) /\ vk_gate_setup_7{2}.`1 < p /\
    vk_gate_setup_7{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_Y_SLOT) /\ vk_gate_setup_7{2}.`2 < p /\
      stateOpening0AtZ{2} = W256.to_uint (stateOpening0AtZ{1}) /\
      stateOpening1AtZ{2} = W256.to_uint (stateOpening1AtZ{1}) /\
      stateOpening2AtZ{2} = W256.to_uint (stateOpening2AtZ{1}) /\
      stateOpening3AtZ{2} = W256.to_uint (stateOpening3AtZ{1}) /\
      poly3_omega{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
      v{2} = W256.to_uint (load mem_0 STATE_V_SLOT) /\
      gate_selector_0_opening{2} = W256.to_uint (load mem_0 PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
      dest{1} = dest_L
      ==>
      (Primops.reverted{1} /\ res{2} = None) \/
      (!Primops.reverted{1} /\
        exists (prev p: int*int) (factor: int) (x96: uint256),
        0 <= p.`1 < Constants.Q /\
        0 <= p.`2 < Constants.Q /\
        res{2} = Some p /\
        Primops.memory{1} = mainGateLinearisation_memory_footprint mem_0 dest_L prev p factor x96
      )
    ].
    proof.
      proc.
      sp.
      seq 1 3: 
      (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\ !failed{2} /\
          Primops.memory{1} = pointMulIntoDest_memory_footprint mem_0 dest{1} vk_gate_setup_0{2} point{2} stateOpening0AtZ{2} /\
          0 <= point{2}.`1 < p /\
          0 <= point{2}.`2 < p /\
          W256.of_int 128 <= dest{1} /\
          W256.of_int 64 <= -dest{1} /\
          W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest{1} /\
          VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest{1} - VK_GATE_SETUP_0_X_SLOT /\
          W256.of_int 64 <= PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /\
          W256.of_int 64 <= STATE_V_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - STATE_V_SLOT /\
          W256.of_int 64 <= PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /\
          vk_gate_setup_1{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_1_X_SLOT) /\ vk_gate_setup_1{2}.`1 < p /\
          vk_gate_setup_1{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_1_Y_SLOT) /\ vk_gate_setup_1{2}.`2 < p /\
          vk_gate_setup_2{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_2_X_SLOT) /\ vk_gate_setup_2{2}.`1 < p /\
          vk_gate_setup_2{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_2_Y_SLOT) /\ vk_gate_setup_2{2}.`2 < p /\
          vk_gate_setup_3{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_3_X_SLOT) /\ vk_gate_setup_3{2}.`1 < p /\
          vk_gate_setup_3{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_3_Y_SLOT) /\ vk_gate_setup_3{2}.`2 < p /\
          vk_gate_setup_4{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_4_X_SLOT) /\ vk_gate_setup_4{2}.`1 < p /\
          vk_gate_setup_4{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_4_Y_SLOT) /\ vk_gate_setup_4{2}.`2 < p /\
          vk_gate_setup_5{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_5_X_SLOT) /\ vk_gate_setup_5{2}.`1 < p /\
          vk_gate_setup_5{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_5_Y_SLOT) /\ vk_gate_setup_5{2}.`2 < p /\
          vk_gate_setup_6{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_X_SLOT) /\ vk_gate_setup_6{2}.`1 < p /\
          vk_gate_setup_6{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_Y_SLOT) /\ vk_gate_setup_6{2}.`2 < p /\
          vk_gate_setup_7{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_X_SLOT) /\ vk_gate_setup_7{2}.`1 < p /\
          vk_gate_setup_7{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_Y_SLOT) /\ vk_gate_setup_7{2}.`2 < p /\
          stateOpening0AtZ{2} = W256.to_uint (stateOpening0AtZ{1}) /\
          stateOpening1AtZ{2} = W256.to_uint (stateOpening1AtZ{1}) /\
          stateOpening2AtZ{2} = W256.to_uint (stateOpening2AtZ{1}) /\
          stateOpening3AtZ{2} = W256.to_uint (stateOpening3AtZ{1}) /\
          poly3_omega{2} = W256.to_uint (load Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
          v{2} = W256.to_uint (load Primops.memory{1} STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          dest{1} = dest_L
        )
      ).
        wp. simplify.
        exists* vk_gate_setup_0{2}, stateOpening0AtZ{2}, dest{1}.
        elim* => vk_gate_setup_0_r stateOpening0AtZ_r dest_l.
        call (pointMulIntoDest_low_equiv_mid vk_gate_setup_0_r.`1 vk_gate_setup_0_r.`2 stateOpening0AtZ_r VK_GATE_SETUP_0_X_SLOT dest_l mem_0).
        skip.
        progress.
        smt (W256.to_uint_cmp).
        smt (W256.to_uint_cmp).
        smt (W256.to_uint_cmp).
        have H_modulus_force: 115792089237316195423570985008687907853269984665640564039457584007913129639936 = W256.modulus by progress.
        rewrite H_modulus_force. smt (W256.to_uint_cmp).
        rewrite /VK_GATE_SETUP_0_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-512)). by progress.
        rewrite /VK_GATE_SETUP_0_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-544)). by progress.
        rewrite H10. by progress.
        have ->: VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 = VK_GATE_SETUP_0_Y_SLOT by progress.
        rewrite H12. by progress.
          case H55. progress.
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          exact vk_gate_setup_separation_mulIntoDest.
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. assumption.
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. assumption.
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. assumption.
          assumption.
          rewrite /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT. simplify.
          do 3! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. assumption.
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. assumption.
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. assumption.
          assumption.
          rewrite /STATE_V_SLOT. simplify.
          do 3! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. assumption.
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. assumption.
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. assumption.
          assumption.
          rewrite /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT. simplify.
          do 3! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          by progress.
          (* end seq *)
      
      seq 1 3: 
      (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\ !failed{2} /\
          (exists (x0 x32 x64 x96),
            Primops.memory{1} = store (store (store (store (store (store mem_0 W256.zero x0) (W256.of_int 32) x32) (W256.of_int 64) x64) (W256.of_int 96) x96) dest{1} (W256.of_int point{2}.`1)) (dest{1} + W256.of_int 32) (W256.of_int point{2}.`2)
          ) /\
          0 <= point{2}.`1 < p /\
          0 <= point{2}.`2 < p /\
          W256.of_int 128 <= dest{1} /\
          W256.of_int 64 <= -dest{1} /\
          W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest{1} /\
          VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest{1} - VK_GATE_SETUP_0_X_SLOT /\
          W256.of_int 64 <= PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /\
          W256.of_int 64 <= STATE_V_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - STATE_V_SLOT /\
          W256.of_int 64 <= PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /\
          vk_gate_setup_2{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_2_X_SLOT) /\ vk_gate_setup_2{2}.`1 < p /\
          vk_gate_setup_2{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_2_Y_SLOT) /\ vk_gate_setup_2{2}.`2 < p /\
          vk_gate_setup_3{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_3_X_SLOT) /\ vk_gate_setup_3{2}.`1 < p /\
          vk_gate_setup_3{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_3_Y_SLOT) /\ vk_gate_setup_3{2}.`2 < p /\
          vk_gate_setup_4{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_4_X_SLOT) /\ vk_gate_setup_4{2}.`1 < p /\
          vk_gate_setup_4{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_4_Y_SLOT) /\ vk_gate_setup_4{2}.`2 < p /\
          vk_gate_setup_5{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_5_X_SLOT) /\ vk_gate_setup_5{2}.`1 < p /\
          vk_gate_setup_5{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_5_Y_SLOT) /\ vk_gate_setup_5{2}.`2 < p /\
          vk_gate_setup_6{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_X_SLOT) /\ vk_gate_setup_6{2}.`1 < p /\
          vk_gate_setup_6{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_Y_SLOT) /\ vk_gate_setup_6{2}.`2 < p /\
          vk_gate_setup_7{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_X_SLOT) /\ vk_gate_setup_7{2}.`1 < p /\
          vk_gate_setup_7{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_Y_SLOT) /\ vk_gate_setup_7{2}.`2 < p /\
          stateOpening0AtZ{2} = W256.to_uint (stateOpening0AtZ{1}) /\
          stateOpening1AtZ{2} = W256.to_uint (stateOpening1AtZ{1}) /\
          stateOpening2AtZ{2} = W256.to_uint (stateOpening2AtZ{1}) /\
          stateOpening3AtZ{2} = W256.to_uint (stateOpening3AtZ{1}) /\
          poly3_omega{2} = W256.to_uint (load Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
          v{2} = W256.to_uint (load Primops.memory{1} STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          dest{1} = dest_L 
        )
      ).
          exists* Primops.reverted{1}.
          elim*=> reverted.
          case reverted.
          conseq (_ : (Primops.reverted{1} /\ failed{2}) ==> (Primops.reverted{1} /\ failed{2})). progress. smt (). progress. smt ().
          call{1} (pointMulAndAddIntoDest_low_pspec_revert).
          wp.
          inline*. wp. skip. progress. left. assumption.
      
          (* case !reverted *)
          exists* vk_gate_setup_1{2}, stateOpening1AtZ{2}, dest{1}, point{2}, Primops.memory{1}.
          elim*=> vk_gate_setup_1_r stateOpening1AtZ_r dest_l point_r mem_1.
          wp.
          call (pointMulAndAddIntoDest_low_equiv_mid vk_gate_setup_1_r.`1 vk_gate_setup_1_r.`2 point_r.`1 point_r.`2 stateOpening1AtZ_r VK_GATE_SETUP_1_X_SLOT dest_l mem_1).
          skip. progress.
          smt (W256.to_uint_cmp).
          smt ().
          smt (W256.to_uint_cmp).
          smt ().
          smt (W256.to_uint_cmp).
          have H_modulus_force: 115792089237316195423570985008687907853269984665640564039457584007913129639936 = W256.modulus by progress.
          rewrite H_modulus_force. smt (W256.to_uint_cmp).
          smt ().
          smt ().
          smt ().
          smt ().
          rewrite /VK_GATE_SETUP_1_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-576)). by progress.
          rewrite /VK_GATE_SETUP_1_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-608)). by progress.
          smt ().
          smt ().
          apply y_coord_in_range. smt (). smt ().
          apply y_coord_in_range_neg. smt (). smt ().
          smt (W256.to_uintK).
          rewrite /VK_GATE_SETUP_1_X_SLOT. simplify.
          rewrite /VK_GATE_SETUP_1_Y_SLOT in H. smt (W256.to_uintK).
          have H_mem: Primops.memory{1} = pointMulIntoDest_memory_footprint mem_0 dest{1} vk_gate_setup_0{2} point{2} stateOpening0AtZ{2} by smt ().
          rewrite H_mem /pointMulIntoDest_memory_footprint. simplify.
          rewrite load_store_diff. rewrite uint256_distrib_sub. rewrite uint256_sub_sub_cancel. rewrite - of_intN. rewrite - (W256.of_int_mod (-32)). by progress.
          rewrite uint256_add_sub_cancel. by progress.
          rewrite load_store_same. reflexivity.
          have H_mem: Primops.memory{1} = pointMulIntoDest_memory_footprint mem_0 dest{1} vk_gate_setup_0{2} point{2} stateOpening0AtZ{2} by smt ().
          rewrite H_mem /pointMulIntoDest_memory_footprint. simplify.
          rewrite load_store_same. reflexivity.
          smt (W256.to_uintK).
          case H24. progress. case H25. progress.
          right. progress.
          smt ().
          exists (W256.of_int (ZModField.asint x)).
          exists (W256.of_int (ZModField.asint y)).
          exists (W256.of_int point{2}.`1).
          exists (W256.of_int point{2}.`2).
          have ->: Primops.memory{1} = pointMulIntoDest_memory_footprint mem_0 dest{1} vk_gate_setup_0{2} point{2} stateOpening0AtZ{2} by smt ().
          exact mulAndAddIntoDest_after_mulIntoDest.
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt ().
          smt ().
          progress.
          smt (). smt (). smt(). smt (). smt (). smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_2_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_2_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_2_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_2_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_3_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_3_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_3_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_3_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_4_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_4_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_4_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_4_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_5_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_5_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_5_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_5_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_6_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_6_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_6_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_6_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          smt ().
          smt ().
          smt ().
          smt ().
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /STATE_V_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          smt ().
          (* failure cases *)
          by progress. by progress.
          (* end seq *)
      
      seq 1 3: 
      (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\ !failed{2} /\
          (exists (x0 x32 x64 x96),
            Primops.memory{1} = store (store (store (store (store (store mem_0 W256.zero x0) (W256.of_int 32) x32) (W256.of_int 64) x64) (W256.of_int 96) x96) dest{1} (W256.of_int point{2}.`1)) (dest{1} + W256.of_int 32) (W256.of_int point{2}.`2)
          ) /\
          0 <= point{2}.`1 < p /\
          0 <= point{2}.`2 < p /\
          W256.of_int 128 <= dest{1} /\
          W256.of_int 64 <= -dest{1} /\
          W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest{1} /\
          VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest{1} - VK_GATE_SETUP_0_X_SLOT /\
          W256.of_int 64 <= PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /\
          W256.of_int 64 <= STATE_V_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - STATE_V_SLOT /\
          W256.of_int 64 <= PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /\
          vk_gate_setup_3{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_3_X_SLOT) /\ vk_gate_setup_3{2}.`1 < p /\
          vk_gate_setup_3{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_3_Y_SLOT) /\ vk_gate_setup_3{2}.`2 < p /\
          vk_gate_setup_4{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_4_X_SLOT) /\ vk_gate_setup_4{2}.`1 < p /\
          vk_gate_setup_4{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_4_Y_SLOT) /\ vk_gate_setup_4{2}.`2 < p /\
          vk_gate_setup_5{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_5_X_SLOT) /\ vk_gate_setup_5{2}.`1 < p /\
          vk_gate_setup_5{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_5_Y_SLOT) /\ vk_gate_setup_5{2}.`2 < p /\
          vk_gate_setup_6{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_X_SLOT) /\ vk_gate_setup_6{2}.`1 < p /\
          vk_gate_setup_6{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_Y_SLOT) /\ vk_gate_setup_6{2}.`2 < p /\
          vk_gate_setup_7{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_X_SLOT) /\ vk_gate_setup_7{2}.`1 < p /\
          vk_gate_setup_7{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_Y_SLOT) /\ vk_gate_setup_7{2}.`2 < p /\
          stateOpening0AtZ{2} = W256.to_uint (stateOpening0AtZ{1}) /\
          stateOpening1AtZ{2} = W256.to_uint (stateOpening1AtZ{1}) /\
          stateOpening2AtZ{2} = W256.to_uint (stateOpening2AtZ{1}) /\
          stateOpening3AtZ{2} = W256.to_uint (stateOpening3AtZ{1}) /\
          poly3_omega{2} = W256.to_uint (load Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
          v{2} = W256.to_uint (load Primops.memory{1} STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          dest{1} = dest_L
        )
      ).
          exists* Primops.reverted{1}.
          elim*=> reverted.
          progress.
          case reverted.
          conseq (_ : (Primops.reverted{1} /\ failed{2}) ==> (Primops.reverted{1} /\ failed{2})). progress. smt (). progress. smt ().
          call{1} (pointMulAndAddIntoDest_low_pspec_revert).
          wp.
          inline*. wp. skip. progress. left. assumption.
      
          (* case !reverted *)
          exists* vk_gate_setup_2{2}, stateOpening2AtZ{2}, dest{1}, point{2}, Primops.memory{1}.
          elim*=> vk_gate_setup_2_r stateOpening2AtZ_r dest_l point_r memory_l.
          wp.
          call (pointMulAndAddIntoDest_low_equiv_mid vk_gate_setup_2_r.`1 vk_gate_setup_2_r.`2 point_r.`1 point_r.`2 stateOpening2AtZ_r VK_GATE_SETUP_2_X_SLOT dest_l memory_l).
          skip. progress.
          smt (W256.to_uint_cmp).
          smt ().
          smt (W256.to_uint_cmp).
          smt ().
          smt (W256.to_uint_cmp).
          have H_modulus_force: 115792089237316195423570985008687907853269984665640564039457584007913129639936 = W256.modulus by progress.
          rewrite H_modulus_force. smt (W256.to_uint_cmp).
          smt ().
          smt ().
          smt ().
          smt ().
          rewrite /VK_GATE_SETUP_2_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-640)). by progress.
          rewrite /VK_GATE_SETUP_2_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-672)). by progress.
          smt ().
          smt ().
          apply y_coord_in_range. smt (). smt ().
          apply y_coord_in_range_neg. smt (). smt ().
          smt (W256.to_uintK).
          rewrite /VK_GATE_SETUP_2_X_SLOT. simplify.
          rewrite /VK_GATE_SETUP_2_Y_SLOT in H. smt (W256.to_uintK).
          have H_mem: Primops.memory{1} =
          store (store (store (store (store (
          store mem_0 W256.zero x0
              ) (W256.of_int 32) x32
            ) (W256.of_int 64) x64
          ) (W256.of_int 96) x96
        ) dest{1} (W256.of_int point{2}.`1)
        ) (dest{1} + (W256.of_int 32)) (W256.of_int point{2}.`2) by smt ().
          rewrite H_mem.
          rewrite load_store_diff. rewrite uint256_distrib_sub. rewrite uint256_sub_sub_cancel. rewrite - of_intN. rewrite - (W256.of_int_mod (-32)). by progress.
          rewrite uint256_add_sub_cancel. by progress.
          rewrite load_store_same. reflexivity.
          have H_mem: Primops.memory{1} =
          store (store (store (store (store (
          store mem_0 W256.zero x0
              ) (W256.of_int 32) x32
            ) (W256.of_int 64) x64
          ) (W256.of_int 96) x96
        ) dest{1} (W256.of_int point{2}.`1)
        ) (dest{1} + (W256.of_int 32)) (W256.of_int point{2}.`2) by smt ().
          rewrite H_mem.
          rewrite load_store_same. reflexivity.
          smt (W256.to_uintK).
          case H24. progress. case H25. progress.
          right. progress.
          smt ().
          exists (W256.of_int (ZModField.asint x)).
          exists (W256.of_int (ZModField.asint y)).
          exists (W256.of_int point{2}.`1).
          exists (W256.of_int point{2}.`2).
          have ->: Primops.memory{1} =
            store (store (store (store (store (
            store mem_0 W256.zero x0
                ) (W256.of_int 32) x32
              ) (W256.of_int 64) x64
            ) (W256.of_int 96) x96
          ) dest{1} (W256.of_int point{2}.`1)
        ) (dest{1} + (W256.of_int 32)) (W256.of_int point{2}.`2) by smt ().
          exact mulAndAddIntoDest_after_mulAndAddIntoDest.
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt ().
          smt ().
          smt (). smt (). smt (). smt (). smt (). smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_3_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_3_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_3_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_3_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_4_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_4_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_4_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_4_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_5_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_5_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_5_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_5_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_6_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_6_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_6_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_6_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          smt ().
          smt ().
          smt ().
          smt ().
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /STATE_V_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          smt ().
          (* failure cases *)
          by progress. by progress.
          (* end seq *)
      seq 1 3: 
      (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\ !failed{2} /\
          (exists (x0 x32 x64 x96),
            Primops.memory{1} = store (store (store (store (store (store mem_0 W256.zero x0) (W256.of_int 32) x32) (W256.of_int 64) x64) (W256.of_int 96) x96) dest{1} (W256.of_int point{2}.`1)) (dest{1} + W256.of_int 32) (W256.of_int point{2}.`2)
          ) /\
          0 <= point{2}.`1 < p /\
          0 <= point{2}.`2 < p /\
          W256.of_int 128 <= dest{1} /\
          W256.of_int 64 <= -dest{1} /\
          W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest{1} /\
          VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest{1} - VK_GATE_SETUP_0_X_SLOT /\
          W256.of_int 64 <= PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /\
          W256.of_int 64 <= STATE_V_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - STATE_V_SLOT /\
          W256.of_int 64 <= PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /\
          vk_gate_setup_4{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_4_X_SLOT) /\ vk_gate_setup_4{2}.`1 < p /\
          vk_gate_setup_4{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_4_Y_SLOT) /\ vk_gate_setup_4{2}.`2 < p /\
          vk_gate_setup_5{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_5_X_SLOT) /\ vk_gate_setup_5{2}.`1 < p /\
          vk_gate_setup_5{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_5_Y_SLOT) /\ vk_gate_setup_5{2}.`2 < p /\
          vk_gate_setup_6{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_X_SLOT) /\ vk_gate_setup_6{2}.`1 < p /\
          vk_gate_setup_6{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_Y_SLOT) /\ vk_gate_setup_6{2}.`2 < p /\
          vk_gate_setup_7{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_X_SLOT) /\ vk_gate_setup_7{2}.`1 < p /\
          vk_gate_setup_7{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_Y_SLOT) /\ vk_gate_setup_7{2}.`2 < p /\
          stateOpening0AtZ{2} = W256.to_uint (stateOpening0AtZ{1}) /\
          stateOpening1AtZ{2} = W256.to_uint (stateOpening1AtZ{1}) /\
          stateOpening2AtZ{2} = W256.to_uint (stateOpening2AtZ{1}) /\
          stateOpening3AtZ{2} = W256.to_uint (stateOpening3AtZ{1}) /\
          poly3_omega{2} = W256.to_uint (load Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
          v{2} = W256.to_uint (load Primops.memory{1} STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          dest{1} = dest_L 
        )
      ).
          exists* Primops.reverted{1}.
          elim*=> reverted.
          progress.
          case reverted.
          conseq (_ : (Primops.reverted{1} /\ failed{2}) ==> (Primops.reverted{1} /\ failed{2})). progress. smt (). progress. smt ().
          call{1} (pointMulAndAddIntoDest_low_pspec_revert).
          wp.
          inline*. wp. skip. progress. left. assumption.
      
          (* case !reverted *)
          exists* vk_gate_setup_3{2}, stateOpening3AtZ{2}, dest{1}, point{2}, Primops.memory{1}.
          elim*=> vk_gate_setup_3_r stateOpening3AtZ_r dest_l point_r memory_l.
          wp.
          call (pointMulAndAddIntoDest_low_equiv_mid vk_gate_setup_3_r.`1 vk_gate_setup_3_r.`2 point_r.`1 point_r.`2 stateOpening3AtZ_r VK_GATE_SETUP_3_X_SLOT dest_l memory_l).
          skip. progress.
          smt (W256.to_uint_cmp).
          smt ().
          smt (W256.to_uint_cmp).
          smt ().
          smt (W256.to_uint_cmp).
          have H_modulus_force: 115792089237316195423570985008687907853269984665640564039457584007913129639936 = W256.modulus by progress.
          rewrite H_modulus_force. smt (W256.to_uint_cmp).
          smt ().
          smt ().
          smt ().
          smt ().
          rewrite /VK_GATE_SETUP_3_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-704)). by progress.
          rewrite /VK_GATE_SETUP_3_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-736)). by progress.
          smt ().
          smt ().
          apply y_coord_in_range. smt (). smt ().
          apply y_coord_in_range_neg. smt (). smt ().
          smt (W256.to_uintK).
          rewrite /VK_GATE_SETUP_3_X_SLOT. simplify.
          rewrite /VK_GATE_SETUP_3_Y_SLOT in H. smt (W256.to_uintK).
          have H_mem: Primops.memory{1} =
          store (store (store (store (store (
          store mem_0 W256.zero x0
              ) (W256.of_int 32) x32
            ) (W256.of_int 64) x64
          ) (W256.of_int 96) x96
        ) dest{1} (W256.of_int point{2}.`1)
        ) (dest{1} + (W256.of_int 32)) (W256.of_int point{2}.`2) by smt ().
          rewrite H_mem.
          rewrite load_store_diff. rewrite uint256_distrib_sub. rewrite uint256_sub_sub_cancel. rewrite - of_intN. rewrite - (W256.of_int_mod (-32)). by progress.
          rewrite uint256_add_sub_cancel. by progress.
          rewrite load_store_same. reflexivity.
          have H_mem: Primops.memory{1} =
          store (store (store (store (store (
          store mem_0 W256.zero x0
              ) (W256.of_int 32) x32
            ) (W256.of_int 64) x64
          ) (W256.of_int 96) x96
        ) dest{1} (W256.of_int point{2}.`1)
        ) (dest{1} + (W256.of_int 32)) (W256.of_int point{2}.`2) by smt ().
          rewrite H_mem.
          rewrite load_store_same. reflexivity.
          smt (W256.to_uintK).
          case H24. progress. case H25. progress.
          right. progress.
          smt ().
          exists (W256.of_int (ZModField.asint x)).
          exists (W256.of_int (ZModField.asint y)).
          exists (W256.of_int point{2}.`1).
          exists (W256.of_int point{2}.`2).
          have ->: Primops.memory{1} =
          store (store (store (store (store (
          store mem_0 W256.zero x0
              ) (W256.of_int 32) x32
            ) (W256.of_int 64) x64
          ) (W256.of_int 96) x96
        ) dest{1} (W256.of_int point{2}.`1)
        ) (dest{1} + (W256.of_int 32)) (W256.of_int point{2}.`2) by smt ().
          exact mulAndAddIntoDest_after_mulAndAddIntoDest.
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt ().
          smt ().
          smt (). smt (). smt (). smt (). smt (). smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_4_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_4_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_4_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_4_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_5_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_5_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_5_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_5_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_6_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_6_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_6_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_6_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          smt ().
          smt ().
          smt ().
          smt ().
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /STATE_V_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          smt ().
          (* failure cases *)
          by progress. by progress.
          (* end seq *)        
      seq 2 4: 
      (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\ !failed{2} /\
          (exists (x0 x32 x64 x96),
            Primops.memory{1} = store (store (store (store (store (store mem_0 W256.zero x0) (W256.of_int 32) x32) (W256.of_int 64) x64) (W256.of_int 96) x96) dest{1} (W256.of_int point{2}.`1)) (dest{1} + W256.of_int 32) (W256.of_int point{2}.`2)
          ) /\
          0 <= point{2}.`1 < p /\
          0 <= point{2}.`2 < p /\
          W256.of_int 128 <= dest{1} /\
          W256.of_int 64 <= -dest{1} /\
          W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest{1} /\
          VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest{1} - VK_GATE_SETUP_0_X_SLOT /\
          W256.of_int 64 <= PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /\
          W256.of_int 64 <= STATE_V_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - STATE_V_SLOT /\
          W256.of_int 64 <= PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /\
          vk_gate_setup_5{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_5_X_SLOT) /\ vk_gate_setup_5{2}.`1 < p /\
          vk_gate_setup_5{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_5_Y_SLOT) /\ vk_gate_setup_5{2}.`2 < p /\
          vk_gate_setup_6{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_X_SLOT) /\ vk_gate_setup_6{2}.`1 < p /\
          vk_gate_setup_6{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_Y_SLOT) /\ vk_gate_setup_6{2}.`2 < p /\
          vk_gate_setup_7{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_X_SLOT) /\ vk_gate_setup_7{2}.`1 < p /\
          vk_gate_setup_7{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_Y_SLOT) /\ vk_gate_setup_7{2}.`2 < p /\
          stateOpening0AtZ{2} = W256.to_uint (stateOpening0AtZ{1}) /\
          stateOpening1AtZ{2} = W256.to_uint (stateOpening1AtZ{1}) /\
          stateOpening2AtZ{2} = W256.to_uint (stateOpening2AtZ{1}) /\
          stateOpening3AtZ{2} = W256.to_uint (stateOpening3AtZ{1}) /\
          poly3_omega{2} = W256.to_uint (load Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
          v{2} = W256.to_uint (load Primops.memory{1} STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          dest{1} = dest_L 
        )
      ).
          exists* Primops.reverted{1}.
          elim*=> reverted.
          progress.

          case reverted.
          conseq (_ : (Primops.reverted{1} /\ failed{2}) ==> (Primops.reverted{1} /\ failed{2})). progress. smt (). progress. smt ().
          sp. call{1} (pointMulAndAddIntoDest_low_pspec_revert).
          wp.
          inline*. wp. skip. progress. left. assumption.
      
          (* case !reverted *)
          exists* vk_gate_setup_4{2}, stateOpening0AtZ{2}, stateOpening1AtZ{2}, dest{1}, point{2}, Primops.memory{1}.
          elim*=> vk_gate_setup_4_r stateOpening0AtZ_r stateOpening1AtZ_r dest_l point_r memory_l.
          wp. sp.
          call (pointMulAndAddIntoDest_low_equiv_mid vk_gate_setup_4_r.`1 vk_gate_setup_4_r.`2 point_r.`1 point_r.`2 (stateOpening0AtZ_r * stateOpening1AtZ_r %% Constants.R) VK_GATE_SETUP_4_X_SLOT dest_l memory_l).
          skip. progress.
          smt (W256.to_uint_cmp).
          smt ().
          smt (W256.to_uint_cmp).
          smt ().
          smt (@IntDiv).
          smt (@IntDiv).
          smt ().
          smt ().
          smt ().
          smt ().
          rewrite /VK_GATE_SETUP_4_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-768)). by progress.
          rewrite /VK_GATE_SETUP_4_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-800)). by progress.
          smt ().
          smt ().
          apply y_coord_in_range. smt (). smt ().
          apply y_coord_in_range_neg. smt (). smt ().
          smt (W256.to_uintK).
          rewrite /VK_GATE_SETUP_4_X_SLOT. simplify.
          rewrite /VK_GATE_SETUP_4_Y_SLOT in H. smt (W256.to_uintK).
          have H_mem: Primops.memory{1} =
          store (store (store (store (store (
          store mem_0 W256.zero x0
              ) (W256.of_int 32) x32
            ) (W256.of_int 64) x64
          ) (W256.of_int 96) x96
        ) dest{1} (W256.of_int point{2}.`1)
        ) (dest{1} + (W256.of_int 32)) (W256.of_int point{2}.`2) by smt ().
          rewrite H_mem.
          rewrite load_store_diff. rewrite uint256_distrib_sub. rewrite uint256_sub_sub_cancel. rewrite - of_intN. rewrite - (W256.of_int_mod (-32)). by progress.
          rewrite uint256_add_sub_cancel. by progress.
          rewrite load_store_same. reflexivity.
          have H_mem: Primops.memory{1} =
          store (store (store (store (store (
          store mem_0 W256.zero x0
              ) (W256.of_int 32) x32
            ) (W256.of_int 64) x64
          ) (W256.of_int 96) x96
        ) dest{1} (W256.of_int point{2}.`1)
        ) (dest{1} + (W256.of_int 32)) (W256.of_int point{2}.`2) by smt ().
          rewrite H_mem.
          rewrite load_store_same. reflexivity.
          rewrite /mulmod. simplify. rewrite - Constants.R_int. smt (@W256 @Utils).
          case H25. progress. case H26. progress.
          right. progress.
          smt ().
          exists (W256.of_int (ZModField.asint x)).
          exists (W256.of_int (ZModField.asint y)).
          exists (W256.of_int point{2}.`1).
            exists (W256.of_int point{2}.`2).
            have ->: Primops.memory{1} =
          store (store (store (store (store (
          store mem_0 W256.zero x0
              ) (W256.of_int 32) x32
            ) (W256.of_int 64) x64
          ) (W256.of_int 96) x96
        ) dest{1} (W256.of_int point{2}.`1)
      ) (dest{1} + (W256.of_int 32)) (W256.of_int point{2}.`2) by smt ().
          exact mulAndAddIntoDest_after_mulAndAddIntoDest.
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt ().
          smt ().
          smt (). smt (). smt (). smt (). smt (). smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_5_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_5_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_5_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_5_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_6_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_6_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_6_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_6_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          smt () |
          smt () ].
          smt ().
          smt ().
          smt ().
          smt ().
          smt ().
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /STATE_V_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          smt (@VerifierConsts).
          smt ().
          (* failure cases *)
          by progress. by progress.
          (* end seq *)  
      seq 2 4: 
      (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\ !failed{2} /\
          (exists (x0 x32 x64 x96),
            Primops.memory{1} = store (store (store (store (store (store mem_0 W256.zero x0) (W256.of_int 32) x32) (W256.of_int 64) x64) (W256.of_int 96) x96) dest{1} (W256.of_int point{2}.`1)) (dest{1} + W256.of_int 32) (W256.of_int point{2}.`2)
          ) /\
          0 <= point{2}.`1 < p /\
          0 <= point{2}.`2 < p /\
          W256.of_int 128 <= dest{1} /\
          W256.of_int 64 <= -dest{1} /\
          W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest{1} /\
          VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest{1} - VK_GATE_SETUP_0_X_SLOT /\
          W256.of_int 64 <= PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /\
          W256.of_int 64 <= STATE_V_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - STATE_V_SLOT /\
          W256.of_int 64 <= PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /\
          vk_gate_setup_6{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_X_SLOT) /\ vk_gate_setup_6{2}.`1 < p /\
          vk_gate_setup_6{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_6_Y_SLOT) /\ vk_gate_setup_6{2}.`2 < p /\
          vk_gate_setup_7{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_X_SLOT) /\ vk_gate_setup_7{2}.`1 < p /\
          vk_gate_setup_7{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_Y_SLOT) /\ vk_gate_setup_7{2}.`2 < p /\
          stateOpening0AtZ{2} = W256.to_uint (stateOpening0AtZ{1}) /\
          stateOpening1AtZ{2} = W256.to_uint (stateOpening1AtZ{1}) /\
          stateOpening2AtZ{2} = W256.to_uint (stateOpening2AtZ{1}) /\
          stateOpening3AtZ{2} = W256.to_uint (stateOpening3AtZ{1}) /\
          poly3_omega{2} = W256.to_uint (load Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
          v{2} = W256.to_uint (load Primops.memory{1} STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          dest{1} = dest_L
        )
      ).
          exists* Primops.reverted{1}.
          elim*=> reverted.
          case reverted.
          progress.
          conseq (_ : (Primops.reverted{1} /\ failed{2}) ==> (Primops.reverted{1} /\ failed{2})). by progress. progress. smt ().
          sp. call{1} (pointMulAndAddIntoDest_low_pspec_revert).
          wp.
          inline*. wp. skip. progress. left. assumption.
      
          (* case !reverted *)
          progress.
          exists* vk_gate_setup_5{2}, stateOpening0AtZ{2}, stateOpening2AtZ{2}, dest{1}, point{2}, Primops.memory{1}.
          elim*=> vk_gate_setup_5_r stateOpening0AtZ_r stateOpening2AtZ_r dest_l point_r memory_l.
          wp. sp.
          call (pointMulAndAddIntoDest_low_equiv_mid vk_gate_setup_5_r.`1 vk_gate_setup_5_r.`2 point_r.`1 point_r.`2 (stateOpening0AtZ_r * stateOpening2AtZ_r %% Constants.R) VK_GATE_SETUP_5_X_SLOT dest_l memory_l).
          skip. progress.
          smt (W256.to_uint_cmp).
          smt (W256.to_uint_cmp).
          smt (@IntDiv).
          smt (@IntDiv).
          rewrite /VK_GATE_SETUP_5_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-832)). by progress.
          rewrite /VK_GATE_SETUP_5_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-864)). by progress.
          apply y_coord_in_range. smt (). smt ().
          apply y_coord_in_range_neg. smt (). smt ().
          smt (W256.to_uintK).
          rewrite /VK_GATE_SETUP_5_X_SLOT. simplify.
          rewrite /VK_GATE_SETUP_5_Y_SLOT in H. smt (W256.to_uintK).
          rewrite load_store_diff. rewrite uint256_distrib_sub. rewrite uint256_sub_sub_cancel. rewrite - of_intN. rewrite - (W256.of_int_mod (-32)). by progress.
          rewrite uint256_add_sub_cancel. by progress.
          rewrite load_store_same. reflexivity.
          rewrite load_store_same. reflexivity.
          rewrite /mulmod. simplify. rewrite - Constants.R_int. smt (@W256 @Utils).          
          case H50. progress. case H51. progress.
          right.  progress.
          exists (W256.of_int (ZModField.asint x)).
          exists (W256.of_int (ZModField.asint y)).
          exists (W256.of_int point{2}.`1).
          exists (W256.of_int point{2}.`2).
          exact mulAndAddIntoDest_after_mulAndAddIntoDest.
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_6_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_6_X_SLOT; by progress |
          smt () |
          smt () ].
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_6_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_6_Y_SLOT; by progress |
          smt () |
          smt () ].
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          smt () |
          smt () ].
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          smt () |
          smt () ].
          have ->: forall (a b: int), (a = b) = (b = a) by smt().
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          have ->: forall (a b: int), (a = b) = (b = a) by smt().
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /STATE_V_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          have ->: forall (a b: int), (a = b) = (b = a) by smt().
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          (* failure cases *)
          by progress. by progress.
          (* end seq *)        
      seq 1 3: 
      (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\ !failed{2} /\
          (exists (old_point: int*int),
            Primops.memory{1} = pointAddIntoDest_memory_footprint mem_0 dest{1} old_point vk_gate_setup_6{2} (ZModField.inzmod point{2}.`1, ZModField.inzmod point{2}.`2)
          ) /\
          0 <= point{2}.`1 < p /\
          0 <= point{2}.`2 < p /\
          W256.of_int 128 <= dest{1} /\
          W256.of_int 64 <= -dest{1} /\
          W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest{1} /\
          VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest{1} - VK_GATE_SETUP_0_X_SLOT /\
          W256.of_int 64 <= PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /\
          W256.of_int 64 <= STATE_V_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - STATE_V_SLOT /\
          W256.of_int 64 <= PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /\
          vk_gate_setup_7{2}.`1 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_X_SLOT) /\ vk_gate_setup_7{2}.`1 < p /\
          vk_gate_setup_7{2}.`2 = W256.to_uint (load Primops.memory{1} VK_GATE_SETUP_7_Y_SLOT) /\ vk_gate_setup_7{2}.`2 < p /\
          stateOpening0AtZ{2} = W256.to_uint (stateOpening0AtZ{1}) /\
          stateOpening1AtZ{2} = W256.to_uint (stateOpening1AtZ{1}) /\
          stateOpening2AtZ{2} = W256.to_uint (stateOpening2AtZ{1}) /\
          stateOpening3AtZ{2} = W256.to_uint (stateOpening3AtZ{1}) /\
          poly3_omega{2} = W256.to_uint (load Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
          v{2} = W256.to_uint (load Primops.memory{1} STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          dest{1} = dest_L
        )
      ).
          exists* Primops.reverted{1}.
          elim*=> reverted.
          case reverted.
          progress.
          conseq (_ : (Primops.reverted{1} /\ failed{2}) ==> (Primops.reverted{1} /\ failed{2})). by progress. progress. smt ().
          call{1} (pointAddAssign_low_pspec_revert).
          wp.
          inline*. wp. skip. progress. left. assumption.

          (* case !reverted *)
          progress.
          exists* vk_gate_setup_6{2}, point{2}, dest{1}, Primops.memory{1}.
          elim* => vk_gate_setup_6_r point_r dest_l memory_l.
          wp.
          call (pointAddAssign_low_equiv_into_dest_mid memory_l dest_l VK_GATE_SETUP_6_X_SLOT point_r vk_gate_setup_6_r).
          skip.
          progress.
          rewrite /VK_GATE_SETUP_6_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-896)). by progress.
          smt (W256.to_uint_cmp).
          smt (W256.to_uint_cmp).
          rewrite load_store_diff. rewrite uint256_distrib_sub. rewrite uint256_sub_sub_cancel. rewrite - of_intN. rewrite - (W256.of_int_mod (-32)). by progress.
          rewrite uint256_add_sub_cancel. by progress.
          rewrite load_store_same. rewrite W256.of_uintK. rewrite pmod_small.
          split. smt (). progress. smt (@Constants). reflexivity.
          rewrite load_store_same. rewrite W256.of_uintK. rewrite pmod_small.
          split. smt (). progress. smt (@Constants). reflexivity.
          rewrite /VK_GATE_SETUP_6_X_SLOT. simplify. smt ().
          rewrite H17.
          rewrite /VK_GATE_SETUP_6_X_SLOT /VK_GATE_SETUP_6_Y_SLOT. by progress.
          case H39. progress. right. progress.
          exists (point{2}).
          rewrite /pointAddIntoDest_memory_footprint. simplify.
          rewrite mulAndAddIntoDest_after_mulAndAddIntoDest.
          assumption. assumption.
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          rewrite /pointAddIntoDest_memory_footprint. simplify.
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_X_SLOT; by progress |
          smt () |
          smt () ].
          rewrite /pointAddIntoDest_memory_footprint. simplify.
          apply vk_gate_setup_separation_mulAndAddIntoDest; [
          smt () |
          rewrite /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          rewrite /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_Y_SLOT; by progress |
          smt () |
          smt () ].
          rewrite /pointAddIntoDest_memory_footprint. simplify.
          have ->: forall (a b: int), (a=b)=(b=a) by smt ().
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          rewrite /pointAddIntoDest_memory_footprint. simplify.
          have ->: forall (a b: int), (a=b)=(b=a) by smt ().
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /STATE_V_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          rewrite /pointAddIntoDest_memory_footprint. simplify.
          have ->: forall (a b: int), (a=b)=(b=a) by smt ().
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          by progress.
          (* end seq *)  
      seq 2 3: 
      (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\ !failed{2} /\
          (exists (x0 x32 x64 x96),
            Primops.memory{1} = store (store (store (store (store (store mem_0 W256.zero x0) (W256.of_int 32) x32) (W256.of_int 64) x64) (W256.of_int 96) x96) dest{1} (W256.of_int point{2}.`1)) (dest{1} + W256.of_int 32) (W256.of_int point{2}.`2)
          ) /\
          0 <= point{2}.`1 < p /\
          0 <= point{2}.`2 < p /\
          W256.of_int 128 <= dest{1} /\
          W256.of_int 64 <= -dest{1} /\
          W256.of_int 64 <= VK_GATE_SETUP_0_X_SLOT - dest{1} /\
          VK_GATE_SETUP_7_Y_SLOT - VK_GATE_SETUP_0_X_SLOT + W256.of_int 32 <= dest{1} - VK_GATE_SETUP_0_X_SLOT /\
          W256.of_int 64 <= PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /\
          W256.of_int 64 <= STATE_V_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - STATE_V_SLOT /\
          W256.of_int 64 <= PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT - dest{1} /\
          W256.of_int 32 <= dest{1} - PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /\
          v{2} = W256.to_uint (load Primops.memory{1} STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          dest{1} = dest_L
        )
      ).
          exists* Primops.reverted{1}.
          elim*=> reverted.
          case reverted.
          progress.
          conseq (_ : (Primops.reverted{1} /\ failed{2}) ==> (Primops.reverted{1} /\ failed{2})). by progress. progress. smt ().
          sp. call{1} (pointMulAndAddIntoDest_low_pspec_revert).
          wp.
          inline*. wp. skip. progress. left. assumption.
      
          (* case !reverted *)
          progress.
          exists* vk_gate_setup_7{2}, poly3_omega{2}, dest{1}, point{2}, Primops.memory{1}.
          elim*=> vk_gate_setup_7_r poly3_omega_r dest_l point_r memory_l.
          wp. sp.
          call (pointMulAndAddIntoDest_low_equiv_mid vk_gate_setup_7_r.`1 vk_gate_setup_7_r.`2 point_r.`1 point_r.`2 poly3_omega_r VK_GATE_SETUP_7_X_SLOT dest_l memory_l).
          call{1} (ConcretePrimops.mload_pspec memory_l PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT).
          skip. progress.
          smt (W256.to_uint_cmp).
          smt (W256.to_uint_cmp).
          smt (W256.to_uint_cmp).
          have H_modulus_force: 115792089237316195423570985008687907853269984665640564039457584007913129639936 = W256.modulus by progress.
          rewrite H_modulus_force. smt (W256.to_uint_cmp).
          rewrite /VK_GATE_SETUP_7_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-960)). by progress.
          rewrite /VK_GATE_SETUP_7_X_SLOT. simplify. rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-992)). by progress.
          apply y_coord_in_range. smt (). smt ().
          apply y_coord_in_range_neg. smt (). smt ().
          smt (W256.to_uintK).
          rewrite /VK_GATE_SETUP_7_X_SLOT. simplify.
          rewrite /VK_GATE_SETUP_7_Y_SLOT in H. smt (W256.to_uintK).
          rewrite /pointAddIntoDest_memory_footprint. simplify.
          rewrite load_store_diff. rewrite uint256_distrib_sub. rewrite uint256_sub_sub_cancel. rewrite - of_intN. rewrite - (W256.of_int_mod (-32)). by progress.
          rewrite uint256_add_sub_cancel. by progress.
          rewrite load_store_same.
          have ->: ZModField.asint(ZModField.inzmod (point{2}.`1)) = point{2}.`1.
          rewrite /inzmod. rewrite pmod_small. smt (). smt (@ZModField). reflexivity.
          rewrite /pointAddIntoDest_memory_footprint. simplify.
          rewrite load_store_same.
          have ->: ZModField.asint(ZModField.inzmod (point{2}.`2)) = point{2}.`2.
          rewrite /inzmod. rewrite pmod_small. smt (). smt (@ZModField). reflexivity.
          case H41. progress. case H42. progress.
          right. progress.
          exists (W256.of_int (ZModField.asint x)).
          exists (W256.of_int (ZModField.asint y)).
          exists (W256.of_int point{2}.`1).
          exists (W256.of_int point{2}.`2).
          rewrite /pointAddIntoDest_memory_footprint. simplify.
          exact mulAndAddIntoDest_after_mulAndAddIntoDest.
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          smt (@EllipticCurve).
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /STATE_V_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          rewrite load_store_diff.
          rewrite uint256_le_sub_add_32. smt ().
          rewrite uint256_le_add_32_sub. rewrite (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. smt ().
          rewrite load_store_diff.
          rewrite (uint256_le_le_trans _ (W256.of_int 64) _ ). by progress. smt ().
          smt ().
          rewrite /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT. simplify.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          reflexivity.
          (* failure cases *)
          by progress. by progress.
          (* end seq *)        
          exists* Primops.reverted{1}. elim*=> reverted.
          progress.
          case reverted. progress.
          call{1} pointMulIntoDest_low_pspec_revert.
          rcondt{2} 3. progress. inline*. wp. skip. progress. smt ().
          wp.
          inline*. wp. skip. by progress.
          rcondf{2} 3. progress. inline*. wp. skip. progress. smt ().
          exists* dest{1}, point{2}, v{2}, gate_selector_0_opening{2}, Primops.memory{1}.
          elim* =>dest_l point_r v_r gate_selector_0_opening_r memory_l.
          call (pointMulIntoDest_low_equiv_mid point_r.`1 point_r.`2 (v_r * gate_selector_0_opening_r %% Constants.R) dest_l dest_l memory_l).
          wp.
          call{1} (ConcretePrimops.mload_pspec memory_l PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT).
          call{1} (ConcretePrimops.mload_pspec memory_l STATE_V_SLOT).
          skip. progress.
          smt ().
          smt ().
          smt ().
          smt ().
          smt (@IntDiv).
          smt (pmod_small @Constants).
          smt ().
          smt ().
          apply y_coord_in_range. smt (). smt().
          apply y_coord_in_range_neg. smt (). smt ().
          have H_mem: Primops.memory{1} = store(store(store(store(store(store
          mem_0 W256.zero x0)
              (W256.of_int 32) x32)
            (W256.of_int 64) x64)
          (W256.of_int 96) x96)
            dest{1} (W256.of_int point{2}.`1))
      (dest{1} + W256.of_int 32) (W256.of_int point{2}.`2) by smt ().
        rewrite H_mem.
      rewrite load_store_diff.
        rewrite uint256_distrib_sub. rewrite uint256_sub_sub_cancel. rewrite - of_intN. rewrite - (W256.of_int_mod (-32)). by progress.
        rewrite uint256_add_sub_cancel. by progress.
      rewrite load_store_same. reflexivity.
          have H_mem: Primops.memory{1} = store(store(store(store(store(store
          mem_0 W256.zero x0)
              (W256.of_int 32) x32)
            (W256.of_int 64) x64)
          (W256.of_int 96) x96)
            dest{1} (W256.of_int point{2}.`1))
      (dest{1} + W256.of_int 32) (W256.of_int point{2}.`2) by smt ().
        rewrite H_mem.
        rewrite load_store_same. reflexivity.
      rewrite /mulmod. simplify.
        have ->: W256.to_uint (load Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = gate_selector_0_opening{2}. smt ().
        have ->: W256.to_uint (load Primops.memory{1} STATE_V_SLOT) = v{2}. smt ().
        smt (@Constants).
        case H15. progress.
        exists point{2}.
        exists (ZModField.asint x, ZModField.asint y).
        exists (v{2} * gate_selector_0_opening{2} %% Constants.R).
        exists x96.
        progress.
        smt (@EllipticCurve).
        smt (@Constants @EllipticCurve).
        smt (@EllipticCurve).
        smt (@Constants @EllipticCurve).
        have ->: mainGateLinearisation_memory_footprint mem_0 dest_L point{2} (ZModField.asint x, ZModField.asint y) (v{2} * gate_selector_0_opening{2} %% Constants.R) x96 = pointMulIntoDest_memory_footprint Primops.memory{1} dest_L point{2} (ZModField.asint x, ZModField.asint y) (v{2} * gate_selector_0_opening{2} %% Constants.R).
        rewrite /mainGateLinearisation_memory_footprint. simplify.
          have H_mem: Primops.memory{1} = store(store(store(store(store(store
          mem_0 W256.zero x0)
              (W256.of_int 32) x32)
            (W256.of_int 64) x64)
          (W256.of_int 96) x96)
            dest{1} (W256.of_int point{2}.`1))
      (dest{1} + W256.of_int 32) (W256.of_int point{2}.`2) by smt ().
        rewrite H_mem.
        have ->: forall (m1 m2: mem), (m1=m2)=(m2=m1) by smt().
        have ->: dest_L = dest{1}. smt ().
        apply (mulIntoDest_after_mulAndAddIntoDest mem_0 dest{1} point{2} (ZModField.asint x, ZModField.asint y) (v{2} * gate_selector_0_opening{2} %% Constants.R) x0 x32 x64 x96 (W256.of_int point{2}.`1) (W256.of_int point{2}.`2)). assumption. assumption.
        rewrite /pointMulIntoDest_memory_footprint. simplify. have ->: dest{1} = dest_L. smt (). by progress.
      progress.
    qed.
    
    
    
    
