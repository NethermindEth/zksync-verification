pragma Goals:printall.

require import Array.
require        Constants.
require import EllipticCurve.
require import Logic.
require import Memory.
require import PointAddAssign.
require import PointAddIntoDest.
require import PointNegate.
require import PurePrimops.
require import Real.
require import RevertWithMessage.
require import UInt256.
require import Utils.
require import YulPrimops.
require import Verifier.
require import VerifierConsts.

import MemoryMap.

module PointSubAssign = {
  proc low(p1, p2) =
  {
    var _1, _5, _6, _9, _15, _16;
    _1 <@ Primops.mload(p1);
    Primops.mstore(W256.zero, _1);
    _5 <@ Primops.mload(p1 + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    _6 <@ Primops.mload(p2);
    Primops.mstore(W256.of_int 64, _6);
    _9  <@ Primops.mload(p2 + W256.of_int 32);
    Primops.mstore(W256.of_int 96, _9);
    PointNegate.low(W256.of_int 64);
    _15 <@ Primops.gas();
    _16 <@ Primops.staticcall(_15, W256.of_int 6, W256.zero, W256.of_int 128, p1, W256.of_int 64);
    if ((bool_of_uint256 (PurePrimops.iszero _16)))
    {
      RevertWithMessage.low(W256.of_int 28, (W256.of_int STRING));
    }
  }

  proc mid(p1: int*int, p2: int*int): (int*int) option = {
    var neg_p2, neg_p2_opt, ret;

    neg_p2_opt <@ PointNegate.mid(p2);
    if (neg_p2_opt = None) {
      ret <- None;
    } else {
      neg_p2 <- odflt (0,0) neg_p2_opt;
      ret <@ PointAddIntoDest.mid(p1.`1, p1.`2, neg_p2.`1, neg_p2.`2);
    }
    
    return ret;
  }
}.

(* lemma pointSubAssign_extracted_equiv_low :
    equiv [
    Verifier_1261.usr_pointSubAssign ~ PointSubAssign.low :
      ={arg, glob PointSubAssign} ==>
      ={res, glob PointSubAssign}
    ].
proof.
  proc.
  seq 26 10: (#pre /\ ={_16}).
  inline*. wp. skip. rewrite /Constants.Q. by progress.
  inline*. wp. skip. by progress.
qed. *)

op pointSubAssign_memory_footprint (memory: mem) (p1 p2 x64 x96: uint256) (result: int*int): mem =
  let point1 = (load memory p1, load memory (p1 + W256.of_int 32)) in
  let point2 = (load memory p2, load memory (p2 + W256.of_int 32)) in
  let mem_1 = store memory W256.zero point1.`1 in
  let mem_2 = store mem_1 (W256.of_int 32) point1.`2 in
  let mem_3 = store mem_2 (W256.of_int 64) x64 in
  let mem_4 = store mem_3 (W256.of_int 96) x96 in
  let mem_5 = store mem_4 p1 (W256.of_int result.`1) in
  store mem_5 (p1 + W256.of_int 32) (W256.of_int result.`2).
  
lemma pointSubAssign_low_equiv_mid_fixed (memory: mem) (point_addr_1, point_addr_2: uint256) (point1 point2: int*int) :
    equiv [
      PointSubAssign.low ~ PointSubAssign.mid:
      arg{1}.`1 = point_addr_1 /\
      arg{1}.`2 = point_addr_2 /\
      arg{2}.`1 = point1 /\
      arg{2}.`2 = point2 /\
      Primops.memory{1} = memory /\
      128 <= W256.to_uint point_addr_1 /\
      128 <= W256.to_uint point_addr_2 /\
      64 <= W256.to_uint (-point_addr_1) /\
      64 <= W256.to_uint (-point_addr_2) /\
      W256.to_uint (load Primops.memory{1} point_addr_1) = point1.`1 /\
      W256.to_uint (load Primops.memory{1} (point_addr_1 + W256.of_int 32)) = point1.`2 /\
      W256.to_uint (load Primops.memory{1} point_addr_2) = point2.`1 /\
      W256.to_uint (load Primops.memory{1} (point_addr_2 + W256.of_int 32)) = point2.`2 /\
      0 <= point1.`1 < p /\ 0 <= point1.`2 < p /\ 0 <= point2.`1 < p /\ 0 <= point2.`2 < p /\ 
      !Primops.reverted{1}
      ==>
      (Primops.reverted{1} /\ res{2} = None) \/
      (!Primops.reverted{1} /\ exists (p: int*int) (x64 x96: uint256),
        res{2} = Some p /\
        Primops.memory{1} = pointSubAssign_memory_footprint memory point_addr_1 point_addr_2 x64 x96 p
      )
    ].
    proof.
      proc.
      pose point1_x := load memory point_addr_1.
      pose point1_y := load memory (point_addr_1 + W256.of_int 32).
      pose point2_x := load memory point_addr_2.
      pose point2_y := load memory (point_addr_2 + W256.of_int 32).
      pose mem_1 := store memory W256.zero point1_x.
      have H_mem_1_point_x : forall (point: uint256), 128 <= W256.to_uint point /\ 64 <= W256.to_uint(-point) => load mem_1 point = load memory point.
      progress. rewrite load_store_diff. smt(@W256 @Utils). smt (@W256 @Utils). reflexivity.
      have H_mem_1_point_y : forall (point: uint256), 128 <= W256.to_uint point /\ 64 <= W256.to_uint(-point) => load mem_1 (point + W256.of_int 32) = load memory (point + W256.of_int 32).
      progress. rewrite load_store_diff. smt(@W256 @Utils). smt (@W256 @Utils). reflexivity.
      pose mem_2 := store mem_1 (W256.of_int 32) point1_y.
      have H_mem_2_point_x : forall (point: uint256), 128 <= W256.to_uint point /\ 64 <= W256.to_uint(-point) => load mem_2 point = load memory point.
      progress. rewrite load_store_diff. smt(@W256 @Utils). smt (@W256 @Utils). exact H_mem_1_point_x.
      have H_mem_2_point_y : forall (point: uint256), 128 <= W256.to_uint point /\ 64 <= W256.to_uint(-point) => load mem_2 (point + W256.of_int 32) = load memory (point + W256.of_int 32).
      progress. rewrite load_store_diff. smt(@W256 @Utils). smt (@W256 @Utils). exact H_mem_1_point_y.
      pose mem_3 := store mem_2 (W256.of_int 64) point2_x.
      have H_mem_3_point_x : forall (point: uint256), 128 <= W256.to_uint point /\ 64 <= W256.to_uint(-point) => load mem_3 point = load memory point.
      progress. rewrite load_store_diff. smt(@W256 @Utils). smt (@W256 @Utils). exact H_mem_2_point_x.
      have H_mem_3_point_y : forall (point: uint256), 128 <= W256.to_uint point /\ 64 <= W256.to_uint(-point) => load mem_3 (point + W256.of_int 32) = load memory (point + W256.of_int 32).
      progress. rewrite load_store_diff. smt(@W256 @Utils). smt (@W256 @Utils). exact H_mem_2_point_y.
      pose mem_4 := store mem_3 (W256.of_int 96) point2_y.
      have H_mem_4_point_x : forall (point: uint256), 128 <= W256.to_uint point /\ 64 <= W256.to_uint(-point) => load mem_4 point = load memory point.
      progress. rewrite load_store_diff. smt(@W256 @Utils). smt (@W256 @Utils). exact H_mem_3_point_x.
      have H_mem_4_point_y : forall (point: uint256), 128 <= W256.to_uint point /\ 64 <= W256.to_uint(-point) => load mem_4 (point + W256.of_int 32) = load memory (point + W256.of_int 32).
      progress. rewrite load_store_diff. smt(@W256 @Utils). smt (@W256 @Utils). exact H_mem_3_point_y.
      have H_mem_4_0: load mem_4 W256.zero = point1_x.
      rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite load_store_same. reflexivity.
      have H_mem_4_32: load mem_4 (W256.of_int 32) = point1_y.
      rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite load_store_same. reflexivity.
      have H_mem_4_64: load mem_4 (W256.of_int 64) = point2_x. rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils). rewrite load_store_same. reflexivity.
      have H_mem_4_96: load mem_4 (W256.of_int 96) = point2_y. rewrite load_store_same. reflexivity.
      seq 8 0: (
        p1{1} = point_addr_1 /\
        p2{1} = point_addr_2 /\
        p1{2} = point1 /\
        p2{2} = point2 /\
        Primops.memory{1} = mem_4 /\
        128 <= W256.to_uint point_addr_1 /\
        128 <= W256.to_uint point_addr_2 /\
        64 <= W256.to_uint (-point_addr_1) /\
        64 <= W256.to_uint (-point_addr_2) /\
        W256.to_uint (load Primops.memory{1} point_addr_1) = point1.`1 /\
        W256.to_uint (load Primops.memory{1} (point_addr_1 + W256.of_int 32)) = point1.`2 /\
        W256.to_uint (load Primops.memory{1} point_addr_2) = point2.`1 /\
        W256.to_uint (load Primops.memory{1} (point_addr_2 + W256.of_int 32)) = point2.`2 /\
        p1{2}.`1 = W256.to_uint point1_x /\
        p1{2}.`2 = W256.to_uint point1_y /\
        p2{2}.`1 = W256.to_uint point2_x /\
        p2{2}.`2 = W256.to_uint point2_y /\
        0 <= point1.`1 < p /\ 0 <= point1.`2 < p /\ 0 <= point2.`1 < p /\ 0 <= point2.`2 < p /\ 
       !Primops.reverted{1}
    ).
      call{1} (ConcretePrimops.mstore_pspec mem_3 (W256.of_int 96) point2_y).
      call{1} (ConcretePrimops.mload_pspec mem_3 (point_addr_2 + W256.of_int 32)).
      call{1} (ConcretePrimops.mstore_pspec mem_2 (W256.of_int 64) point2_x).
      call{1} (ConcretePrimops.mload_pspec mem_2 point_addr_2).
      call{1} (ConcretePrimops.mstore_pspec mem_1 (W256.of_int 32) point1_y).
      call{1} (ConcretePrimops.mload_pspec mem_1 (point_addr_1 + W256.of_int 32)).
      call{1} (ConcretePrimops.mstore_pspec memory W256.zero point1_x).
      call{1} (ConcretePrimops.mload_pspec memory point_addr_1).
        skip. progress.
        exact H_mem_1_point_y. exact H_mem_2_point_x. exact H_mem_3_point_y.
        rewrite - / mem_4. rewrite H_mem_4_point_x. smt (). smt ().
        rewrite - /mem_4. rewrite H_mem_4_point_y. smt (). smt ().
        rewrite - / mem_4. rewrite H_mem_4_point_x. smt (). smt ().
        rewrite - /mem_4. rewrite H_mem_4_point_y. smt (). smt ().
        smt (). smt (). smt (). smt ().
    seq 1 1: (
      (Primops.reverted{1} /\ neg_p2_opt{2} = None) \/
      (
        p1{1} = point_addr_1 /\
        !Primops.reverted{1} /\
        p1{2}.`1 = W256.to_uint point1_x /\
        p1{2}.`2 = W256.to_uint point1_y /\
        p2{2}.`1 = W256.to_uint point2_x /\
        p2{2}.`2 = W256.to_uint point2_y /\
        0 <= p1{2}.`1 < p /\ 0 <= p1{2}.`2 < p /\ 0 <= p2{2}.`1 < p /\ 0 <= p2{2}.`2 < p /\
        exists neg_point,
          neg_p2_opt{2} = Some neg_point /\
          0 <= neg_point.`1 < Constants.Q /\ 0 <= neg_point.`2 < Constants.Q /\
          Primops.memory{1} = store (store mem_4 (W256.of_int 64) (W256.of_int neg_point.`1)) (W256.of_int 96) (W256.of_int neg_point.`2)
      )
    ).
    call{1} (pointNegate_low_equiv_mid mem_4 (W256.of_int 64) point2.`1 point2.`2).
    skip. progress. smt (). smt (@Constants). smt (@Constants). smt (). smt (). smt ().
    
    case (Primops.reverted{1}).
      rcondt{2} 1. progress. skip. progress. smt ().
      inline Primops.gas. sp.
      seq 1 0: (Primops.reverted{1} /\ ret{2} = None). call{1} (ConcretePrimops.staticcall_pspec_revert). skip. by progress.
      if{1}. call{1} (revertWithMessage_low_pspec). skip. by progress.
      skip. by progress.
    (* !Primops.reverted{1} *)
      rcondf{2} 1. progress. skip. progress. smt ().
      inline PointAddIntoDest.mid.
      inline Primops.gas Primops.staticcall.
      rcondf{1} 8. progress. wp. skip. progress. smt (@W256 @Utils).
      rcondt{1} 8. progress. wp. skip. by progress.
      rcondt{1} 8. progress. wp. skip. by progress.
      seq 11 5: (
        x1{2} = W256.to_uint x1{1} /\
        x2{2} = W256.to_uint x2{1} /\
        y1{2} = W256.to_uint y1{1} /\
        y2{2} = W256.to_uint y2{1} /\
        0 <= x1{2} < p /\ 0 <= x2{2} < p /\ 0 <= y1{2} < p /\ 0 <= y2{2} < p /\
        Primops.memory{1} = store (store mem_4 (W256.of_int 64) x2{1}) (W256.of_int 96) y2{1} /\
        !Primops.reverted{1} /\
        retOff{1} = point_addr_1
      ).
        inline Primops.mload. wp. skip.
        move=> &1 &2 H.
        have H_post_negate: exists neg_point,
          neg_p2_opt{2} = Some neg_point /\
          0 <= neg_point.`1 < Constants.Q /\ 0 <= neg_point.`2 < Constants.Q /\
          Primops.memory{1} = store (store mem_4 (W256.of_int 64) (W256.of_int neg_point.`1)) (W256.of_int 96) (W256.of_int neg_point.`2).
            smt ().
        case H_post_negate.
        move => neg_point H_post_negate.
        pose mem_post_negate := store (store mem_4 (W256.of_int 64) (W256.of_int neg_point.`1)) (W256.of_int 96) (W256.of_int neg_point.`2).
        have H_mem_post_negate: Primops.memory{1} = mem_post_negate. smt ().
        rewrite H_mem_post_negate.
        progress.
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite H_mem_4_0. smt ().
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite load_store_same. rewrite W256.of_uintK. rewrite pmod_small. smt (). smt ().
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite H_mem_4_32. smt ().
        rewrite load_store_same. smt (@W256 @Utils @Constants).
          smt (). smt (). smt (). smt (@Constants). smt (). smt (@Constants). smt (). smt (@Constants).
        rewrite /mem_post_negate. rewrite load_store_same. congr. congr. rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils). rewrite load_store_same. reflexivity. smt (). smt ().
      rcondf{1} 5. progress. wp. skip. progress.
      have H_x1: x1{hr} = x1{hr} %% (W256.of_int p).
        rewrite /W256.\umod /W256.ulift2. rewrite W256.of_uintK. rewrite pmod_small. progress. rewrite pmod_small. progress.
        smt (@Constants). smt (@Constants). smt (). rewrite W256.to_uintK. reflexivity.
      have H_y1: y1{hr} = y1{hr} %% (W256.of_int p).
        rewrite /W256.\umod /W256.ulift2. rewrite W256.of_uintK. rewrite pmod_small. progress. rewrite pmod_small. progress.
        smt (@Constants). smt (@Constants). smt (). rewrite W256.to_uintK. reflexivity.
      have H_x2: x2{hr} = x2{hr} %% (W256.of_int p).
        rewrite /W256.\umod /W256.ulift2. rewrite W256.of_uintK. rewrite pmod_small. progress. rewrite pmod_small. progress.
        smt (@Constants). smt (@Constants). smt (). rewrite W256.to_uintK. reflexivity.
      have H_y2: y2{hr} = y2{hr} %% (W256.of_int p).
        rewrite /W256.\umod /W256.ulift2. rewrite W256.of_uintK. rewrite pmod_small. progress. rewrite pmod_small. progress.
        smt (@Constants). smt (@Constants). smt (). rewrite W256.to_uintK. reflexivity.
        smt ().
      
      seq 4 4: (
        #pre /\
        ={x1_F, y1_F, x2_F, y2_F} /\
        x1_F{2} = ZModField.inzmod x1{2} /\
        y1_F{2} = ZModField.inzmod y1{2} /\
        x2_F{2} = ZModField.inzmod x2{2} /\
        y2_F{2} = ZModField.inzmod y2{2}
      ). wp. skip. by progress.
      if{1}.
      (*failure case*)
        rcondt{1} 3. progress. wp. skip. progress. rewrite /iszero /bool_of_uint256. smt (@W256 @Utils).
        call{1} (revertWithMessage_low_pspec). wp. skip. progress. left. progress. smt (@EllipticCurve).
      (*success case*)
        seq 1 1: (#pre /\ ={result} (* /\ result{1} = ecAdd_precompile x1_F{1} y1_F{1} x2_F{1} y2_F{1}*) ). wp. skip. by progress.
        if{1}. sp. rcondt{1} 1. progress. skip. progress. rewrite /iszero /bool_of_uint256. smt (@W256 @Utils).
          call{1} (revertWithMessage_low_pspec). wp. skip. progress. left. progress.
          have H_none: forall (a: (F*F) option), is_none a => a = None. smt ().
          smt ().
        inline Primops.mstore. sp.
        rcondf{1} 1. progress. skip. progress. rewrite /iszero /bool_of_uint256. smt ().
        skip. progress.
        right.
        progress.
          rewrite /pointSubAssign_memory_footprint. progress.
          rewrite /mem_4 /mem_3.
          rewrite (store_store_swap_diff mem_2 _ _ _ _). smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite store_store_same. rewrite (store_store_swap_diff mem_2 _ _ _ _). smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite /mem_2 /mem_1. rewrite - /point1_x. rewrite - /point1_y.
          rewrite store_store_same.
          exists (F_to_int_point (odflt (ZModField.zero, ZModField.zero) result{2})).
          exists x2{1}.
          exists y2{1}.
          progress.
          have H_res: exists (r: F*F), result{2} = Some r. smt ().
          case H_res. by progress.
      qed.

