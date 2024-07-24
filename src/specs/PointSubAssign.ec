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

op to_point (p: int*int): (F*F) = (ZModField.inzmod p.`1, ZModField.inzmod p.`2).
op from_point (p: F*F): int*int = (ZModField.asint p.`1, ZModField.asint p.`2).

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

op pointSubAssign_memory_footprint (memory: mem) (p1 p2: uint256): mem =
  let point1 = (load memory p1, load memory (p1 + W256.of_int 32)) in
  let point2 = (load memory p2, load memory (p2 + W256.of_int 32)) in
  let mem_1 = store memory W256.zero point1.`1 in
  let mem_2 = store mem_1 (W256.of_int 32) point1.`2 in
  let mem_3 = store mem_2 (W256.of_int 64) point2.`1 in
  let mem_4 = store mem_3 (W256.of_int 96) (-(point2.`2) %% (W256.of_int Constants.Q)) in
  let mem_5 = store mem_4 p1 (ConcretePrimops.ecAdd_precompile_unsafe_cast point1 point2).`1 in
  store mem_5 (p1 + W256.of_int 32) (ConcretePrimops.ecAdd_precompile_unsafe_cast point1 point2).`2.

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
      !Primops.reverted{1}
      ==>
      (Primops.reverted{1} /\ res{2} = None) \/
      (!Primops.reverted{1} /\ exists p,
        res{2} = Some p /\
        Primops.memory{1} = pointSubAssign_memory_footprint memory point_addr_1 point_addr_2
      )
    ].
    proof.
      proc.
      pose point1_x := load memory point_addr_1.
      pose point1_y := load memory (point_addr_1 + W256.of_int 32).
      pose point2_x := load memory point_addr_2.
      pose point2_y := load memory (point_addr_2 + W256.of_int 32).
      pose mem_1 := store memory W256.zero point1_x.
      pose mem_2 := store mem_1 (W256.of_int 32) point1_y.
      pose mem_3 := store mem_2 (W256.of_int 64) point2_x.
      pose mem_4 := store mem_3 (W256.of_int 96) point2_y.
      seq 2 0: (
        p1{1} = point_addr_1 /\
        p2{1} = point_addr_2 /\
        p1{2} = point1 /\
        p2{2} = point2 /\
        Primops.memory{1} = mem_1 /\
        128 <= W256.to_uint point_addr_1 /\
        128 <= W256.to_uint point_addr_2 /\
        64 <= W256.to_uint (-point_addr_1) /\
        64 <= W256.to_uint (-point_addr_2) /\
        W256.to_uint (load Primops.memory{1} point_addr_1) = point1.`1 /\
        W256.to_uint (load Primops.memory{1} (point_addr_1 + W256.of_int 32)) = point1.`2 /\
        W256.to_uint (load Primops.memory{1} point_addr_2) = point2.`1 /\
        W256.to_uint (load Primops.memory{1} (point_addr_2 + W256.of_int 32)) = point2.`2 /\
       !Primops.reverted{1}
      ).
      call{1} (ConcretePrimops.mstore_pspec memory W256.zero point1_x).
      call{1} (ConcretePrimops.mload_pspec memory point_addr_1).
      skip. progress.
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      seq 2 0: (
        p1{1} = point_addr_1 /\
        p2{1} = point_addr_2 /\
        p1{2} = point1 /\
        p2{2} = point2 /\
        Primops.memory{1} = mem_2 /\
        128 <= W256.to_uint point_addr_1 /\
        128 <= W256.to_uint point_addr_2 /\
        64 <= W256.to_uint (-point_addr_1) /\
        64 <= W256.to_uint (-point_addr_2) /\
        W256.to_uint (load Primops.memory{1} point_addr_1) = point1.`1 /\
        W256.to_uint (load Primops.memory{1} (point_addr_1 + W256.of_int 32)) = point1.`2 /\
        W256.to_uint (load Primops.memory{1} point_addr_2) = point2.`1 /\
        W256.to_uint (load Primops.memory{1} (point_addr_2 + W256.of_int 32)) = point2.`2 /\
       !Primops.reverted{1}
      ).
      call{1} (ConcretePrimops.mstore_pspec mem_1 (W256.of_int 32) point1_y).
      call{1} (ConcretePrimops.mload_pspec mem_1 (point_addr_1 + W256.of_int 32)).
      skip. progress.
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      seq 2 0: (
        p1{1} = point_addr_1 /\
        p2{1} = point_addr_2 /\
        p1{2} = point1 /\
        p2{2} = point2 /\
        Primops.memory{1} = mem_3 /\
        128 <= W256.to_uint point_addr_1 /\
        128 <= W256.to_uint point_addr_2 /\
        64 <= W256.to_uint (-point_addr_1) /\
        64 <= W256.to_uint (-point_addr_2) /\
        W256.to_uint (load Primops.memory{1} point_addr_1) = point1.`1 /\
        W256.to_uint (load Primops.memory{1} (point_addr_1 + W256.of_int 32)) = point1.`2 /\
        W256.to_uint (load Primops.memory{1} point_addr_2) = point2.`1 /\
        W256.to_uint (load Primops.memory{1} (point_addr_2 + W256.of_int 32)) = point2.`2 /\
       !Primops.reverted{1}
      ).
      call{1} (ConcretePrimops.mstore_pspec mem_2 (W256.of_int 64) point2_x).
      call{1} (ConcretePrimops.mload_pspec mem_2 point_addr_2).
      skip. progress.
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
      rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().      

















          call{1} (ConcretePrimops.mstore_pspec mem_3 (W256.of_int 96) point2_y).
        call{1} (ConcretePrimops.mload_pspec mem_3 (point_addr_2 + W256.of_int 32)).



        skip. progress.
        rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt().
        rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils).
        rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
        rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils).
        rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils).
        rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils). smt ().
        rewrite load_store_diff.
        clear H20 H19 H18 H17 H16 H15 H14 H13 H12 H11 H10 H9 H8 H7. smt (@W256 @Utils).
        clear H20 H19 H18 H17 H16 H15 H14 H13 H12 H11 H10 H9 H8 H7. smt (@W256 @Utils).
        rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils).
        rewrite load_store_diff. clear H20 H18 H16 H14. smt(@W256 @Utils). smt(@W256 @Utils).
        rewrite load_store_diff. smt(@W256 @Utils). smt(@W256 @Utils).
      case (point2_y = W256.zero /\ point2_x <> W256.zero).
          seq 0 2: (ret{2} = None).
          inline PointNegate.mid.
          rcondt{2} 2. progress. wp. skip. progress.




lemma pointSubAssign_low_equiv_mid_fail_case (memory: mem) (point_addr_1, point_addr_2: uint256) (point1 point2: int*int) :
    point2.`2 = 0 =>
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
      !Primops.reverted{1}
      ==>
      (Primops.reverted{1} /\ res{2} = None) \/
      (!Primops.reverted{1} /\ exists p,
        res{2} = Some p /\
        Primops.memory{1} = pointSubAssign_memory_footprint memory
      )
    ].
    proof.
    move=>H_y_eq_0.
      proc.
      seq 9 0: (load Primops.memory{1} (W256.of_int 96) = W256.of_int Constants.Q /\ p2{2} = point2).
      inline Primops.gas. wp.
      inline Primops.mstore Primops.mload. wp. skip.
      progress.
      pose mem_1 := store Primops.memory{1} W256.zero (load Primops.memory{1} p1{1}).
      pose mem_2 := store mem_1 (W256.of_int 32) (load mem_1 (p1{1} + W256.of_int 32)).
      pose mem_3 := store mem_2 (W256.of_int 64) (load mem_2 p2{1}).
      rewrite load_store_same.
      have H_load_eq_0 : load mem_3 (p2{1} + (W256.of_int 32)) = W256.zero.
      rewrite /mem_3. rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite /mem_2. rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite /mem_1. rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
      smt (@W256 @Utils).
      rewrite H_load_eq_0. smt (@W256 @Utils).
      seq 1 0: (_16{1} = W256.zero /\ p2{2} = point2).
      exists* Primops.memory{1}.
      elim*=>memory_pre_staticcall.
      exists* p1{1}.
      elim*=>p1_addr.
      call{1} (
        ConcretePrimops.staticcall_ec_add_pspec
        memory_pre_staticcall
        ((load memory_pre_staticcall W256.zero),
        (load memory_pre_staticcall (W256.of_int 32)))
        ((load memory_pre_staticcall (W256.of_int 64)),
        W256.of_int Constants.Q)
        W256.zero
        p1_addr
      ).
          skip.
          progress. smt ().
          have H_staticcall_should_not_success : forall (a b c: uint256), ! (ConcretePrimops.staticcall_ec_add_should_succeed (a, b) (c, W256.of_int Constants.Q)).
          progress. rewrite /ConcretePrimops.staticcall_ec_add_should_succeed.
          have H_not_wellformed: !ConcretePrimops.point_wellformed(c, W256.of_int Constants.Q).
          rewrite /point_wellformed.
          simplify.
          have H_Q_neq_q_mod_p : W256.of_int Constants.Q <> (W256.of_int Constants.Q %% W256.of_int p).
          rewrite Constants.q_eq_elliptic_curve_p. rewrite /W256.\umod. rewrite /W256.ulift2. smt. smt(). smt(). smt().
      rcondt{1} 1. progress. skip. rewrite /iszero /bool_of_uint256. progress. smt (@W256 @Utils).
      call{1} revertWithMessage_low_pspec.
      rcondt{2} 1. by progress.
      wp. skip. by progress.
    qed.

  lemma pointSubAssign_low_equiv_mid_success_case (memory: mem) (point_addr_1, point_addr_2) (point1 point2: int*int) :
      point2.`2 <> 0 =>
      equiv [
        PointSubAssign.low ~ PointSubAssign.mid:
        arg{1}.`1 = point_addr_1 /\
        arg{1}.`2 = point_addr_2 /\
        arg{2}.`1 = point1 /\
        arg{2}.`2 = point2 /\
        0 <= point1.`1 < p /\ 0 <= point1.`2 < p /\ 0 <= point2.`1 < p /\ 0 <= point2.`2 < p /\
        Primops.memory{1} = memory /\
        128 <= W256.to_uint point_addr_1 /\
        128 <= W256.to_uint point_addr_2 /\
        64 <= W256.to_uint (-point_addr_1) /\
        64 <= W256.to_uint (-point_addr_2) /\
        W256.to_uint (load Primops.memory{1} point_addr_1) = point1.`1 /\
        W256.to_uint (load Primops.memory{1} (point_addr_1 + W256.of_int 32)) = point1.`2 /\
        W256.to_uint (load Primops.memory{1} point_addr_2) = point2.`1 /\
        W256.to_uint (load Primops.memory{1} (point_addr_2 + W256.of_int 32)) = point2.`2 /\
        !Primops.reverted{1}
        ==>
        (Primops.reverted{1} /\ res{2} = None) \/
        (!Primops.reverted{1} /\ exists p,
          res{2} = Some p /\
          Primops.memory{1} = pointSubAssign_memory_footprint memory
        )
      ].
      proof.
      move=> H_y_neq_0.
        proc.
        rcondf{2} 1. by progress.
        inline PointNegate.mid.
        sp. simplify.
        inline PointAddIntoDest.mid.
        pose mem_1 := store memory W256.zero (load memory point_addr_1).
        pose mem_2 := store mem_1 (W256.of_int 32) (load memory (point_addr_1 + W256.of_int 32)).
        pose mem_3 := store mem_2 (W256.of_int 64) (load memory point_addr_2).
        pose mem_4 := store mem_3 (W256.of_int 96) (W256.of_int Constants.Q - (load memory (point_addr_2 + W256.of_int 32))).
        seq 9 0: (
          Primops.memory{1} = mem_4 /\
          p1{1} = point_addr_1 /\
          W256.to_uint (load memory point_addr_1) = point1.`1 /\
          W256.to_uint (load memory (point_addr_1 + W256.of_int 32)) = point1.`2 /\
          W256.to_uint (load memory point_addr_2) = point2.`1 /\
          W256.to_uint (load memory (point_addr_2 + W256.of_int 32)) = point2.`2 /\
          0 <= point1.`1 < p /\ 0 <= point1.`2 < p /\ 0 <= point2.`1 < p /\ 0 <= point2.`2 < p
        ).
        inline Primops.gas. wp.
        call{1} (ConcretePrimops.mstore_pspec mem_3 (W256.of_int 96) (W256.of_int Constants.Q - (load memory (point_addr_2 + W256.of_int 32)))).
        call{1} (ConcretePrimops.mload_pspec mem_3 (point_addr_2 + W256.of_int 32)).
        call{1} (ConcretePrimops.mstore_pspec mem_2 (W256.of_int 64) (load memory point_addr_2)).
        call{1} (ConcretePrimops.mload_pspec mem_2 point_addr_2).
        call{1} (ConcretePrimops.mstore_pspec mem_1 (W256.of_int 32) (load memory (point_addr_1 + W256.of_int 32))).
        call{1} (ConcretePrimops.mload_pspec mem_1 (point_addr_1 + W256.of_int 32)).
        call{1} (ConcretePrimops.mstore_pspec memory W256.zero (load memory point_addr_1)).
        call{1} (ConcretePrimops.mload_pspec memory point_addr_1).
        skip.
        progress. smt (). smt().
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils). reflexivity.
        smt ().
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils). reflexivity.
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils). reflexivity.
        smt (). smt(). smt(). smt(). smt (). smt (). smt (). smt (). smt (). smt (). smt (). smt ().
        seq 1 0: (_16{1} = W256.one).
        exists* Primops.memory{1}, p1{1}.
        elim* => memory_pre_staticcall p_addr_1.
        call{1} (
          ConcretePrimops.staticcall_ec_add_pspec
          memory_pre_staticcall
          (load memory_pre_staticcall W256.zero, load memory_pre_staticcall (W256.of_int 32))
          (load memory_pre_staticcall (W256.of_int 64), load memory_pre_staticcall (W256.of_int 96))
          W256.zero
          p_addr_1
        ).
            skip.
            progress.
            have H_should_succeed: ConcretePrimops.staticcall_ec_add_should_succeed
              ((load mem_4 W256.zero), (load mem_4 (W256.of_int 32)))
              ((load mem_4 (W256.of_int 64)), (load mem_4 (W256.of_int 96))).
                rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
                rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
                rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
                rewrite load_store_same.
                rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
                rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
                rewrite load_store_same.
                rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
                rewrite load_store_same.
                rewrite load_store_same.
                rewrite /staticcall_ec_add_should_succeed.
                rewrite /point_wellformed. progress. rewrite - W256.to_uintK H. rewrite /W256.\umod /W256.ulift2. rewrite W256.of_uintK W256.of_uintK.
                rewrite pmod_small. progress. smt (@W256 @Utils @IntDiv).
                rewrite pmod_small. progress. smt (@Constants).
                rewrite pmod_small. progress. smt (@Constants). smt(@Constants). smt().
                rewrite pmod_small. smt (@Constants @W256 @Utils @IntDiv). reflexivity.
                rewrite - W256.to_uintK. rewrite H0. smt (@Constants @W256 @IntDiv @Utils).
                rewrite - W256.to_uintK H1. smt (@Constants @W256 @IntDiv @Utils).
                rewrite /W256.\umod /W256.ulift2. rewrite W256.of_uintK.
                rewrite pmod_small. progress. smt (@W256).
                rewrite pmod_small. smt (@Constants).
                have H_y: load memory (point_addr_2 + (W256.of_int 32)) = W256.of_int point2.`2. smt (@W256 @Utils).
                rewrite H_y. smt (@Constants @W256 @Utils).
                smt (@W256).
                



              
                rewrite - W256.to_uintK. smt (@Constants @W256 @IntDiv @Utils).
                simplify.
                rewrite /point_wellformed.
                simplify.
                do rewrite H.
                do rewrite H1.
                do rewrite H2.
        
      
    
