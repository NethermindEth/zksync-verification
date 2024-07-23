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
    Primops.mstore(W256.of_int 96, W256.of_int Constants.Q - _9);
    _15 <@ Primops.gas();
    _16 <@ Primops.staticcall(_15, W256.of_int 6, W256.zero, W256.of_int 128, p1, W256.of_int 64);
    if ((bool_of_uint256 (PurePrimops.iszero _16)))
    {
      RevertWithMessage.low(W256.of_int 28, (W256.of_int STRING));
    }
  }

  proc low'(p1, p2) = {
    var _1, _5, _6, _9;
    _1 <@ Primops.mload(p1);
    Primops.mstore(W256.zero, _1);
    _5 <@ Primops.mload(p1 + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    _6 <@ Primops.mload(p2);
    Primops.mstore(W256.of_int 64, _6);
    _9 <@ Primops.mload(p2 + W256.of_int 32);
    Primops.mstore(W256.of_int 96, _9);
    PointNegate.low(W256.of_int 64);
    PointAddIntoDest.low(W256.zero, W256.of_int 64, p1);
  }

  proc mid(p1: int*int, p2: int*int): (int*int) option = {
    var neg_p2, neg_p2_opt, ret;

    if (p2.`2 = 0) {
      ret <- None;
    } else {
      neg_p2_opt <@ PointNegate.mid(p2); (* PointNegate guaranteed to succeed here *)
      neg_p2 <- odflt (0,0) neg_p2_opt;
      ret <@ PointAddIntoDest.mid(p1.`1, p1.`2, neg_p2.`1, neg_p2.`2);
    }
    
    return ret;
  }
}.

lemma pointSubAssign_extracted_equiv_low :
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
qed.

lemma pointSubAssign_low_equiv_low' :
    equiv [
      PointSubAssign.low ~ PointSubAssign.low':
      ={arg, glob PointSubAssign} ==>
      (Primops.reverted{1} /\ Primops.reverted{2}) \/
      ={res, glob PointSubAssign}
    ].
    proof.
      proc.
      seq 7 7: (#pre /\ ={_9}). inline*. wp. skip. by progress.
      inline PointAddIntoDest.low.
    case (_9{1} = W256.zero).
      seq 4 0: (Primops.reverted{1}).
      inline Primops.mstore Primops.gas.
      exists* p1{1}.
      sp. elim* => memory p1.
      seq 1 0: (_16{1} = W256.zero).
      call{1} (
        ConcretePrimops.staticcall_ec_add_pspec
        (store memory (W256.of_int 96) (W256.of_int Constants.Q))
        (load memory W256.zero, load memory (W256.of_int 32))
        (load memory (W256.of_int 64), W256.of_int Constants.Q)
        W256.zero
        p1
      ).
          skip. progress.
          rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils). reflexivity.
          rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils). reflexivity.
          rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils). reflexivity.
          rewrite load_store_same. reflexivity.
      apply (weaken_and_left (result = W256.zero) (memory_L = store Primops.memory{2} (W256.of_int 96) (W256.of_int Constants.Q))).
          apply H4. rewrite /staticcall_ec_add_should_succeed.
          have H_malformed: !(ConcretePrimops.point_wellformed (load Primops.memory{2} (W256.of_int 64), W256.of_int Constants.Q)).
      rewrite /point_wellformed.
      


    
      seq 8 0: (load Primops.memory{1} (W256.of_int 96) = (W256.of_int Constants.Q)).
      inline*. wp. skip. progress. rewri
      seq 8 9: ((Primops.reverted{1} /\ Primops.reverted{2}
      (* exists* Primops.memory{2}, p1{2}, p2{2}.
      elim*=> memory p1 p2.
      pose p1_x := load memory p1.
      pose p1_y := load memory (p1 + W256.of_int 32).
      pose p2_x := load memory p2.
      pose p2_y := load memory (p2 + W256.of_int 32).
      pose mem_1 := store memory W256.zero p1_x.
      pose mem_2 := store mem_1 (W256.of_int 32) p1_y.
      pose mem_3 := store mem_2 (W256.of_int 64) p2_x.
      seq 7 7: (
        Primops.memory{1} = mem_3 /\ Primops.memory{2} = mem_3 /\
        _9{1} = p2_y /\ _9{2} = p2_y
      ). inline*. wp. skip. progress. *)
        seq 1 2: ((Primops.reverted{1} /\ Primops.reverted{2}) \/ ={Primops.memory}).
      inline Primops.mstore. sp.
      call{2} (pointNegate_low_equiv_mid Primops.memory{2} (W256.of_int 64).

op pointSubAssign_memory_footprint (memory: mem) (p1: uint256): mem. (* =
  let mem_1 = store memory W256.zero (load memory p1) in
  let mem_2 = store mem_1 (W256.of_int 32) (load memory (p1 + W256.of_int 32)) in
  let mem_*)

lemma pointSubAssign_low_equiv_mid (memory: mem) (p1_addr: uint256) :
    equiv [
      PointSubAssign.low ~ PointSubAssign.mid:
      !Primops.reverted{1} /\
      Primops.memory{1} = memory /\
      arg{1}.`1 = p1_addr /\
      W256.to_uint (load memory arg{1}.`1) = arg{2}.`1.`1 /\
      W256.to_uint (load memory (arg{1}.`1 + W256.of_int 32)) = arg{2}.`1.`2 /\
      W256.to_uint (load memory arg{1}.`2) = arg{2}.`2.`1 /\
      W256.to_uint (load memory (arg{1}.`2 + W256.of_int 32)) = arg{2}.`2.`2 /\
      ! (arg{2}.`2.`1 <> 0 /\ arg{2}.`2.`2 = 0) ==>
      (res{2} = None /\ Primops.reverted{1}) \/
      (exists p,
        res{2} = Some p /\
        !Primops.reverted{1} /\
        Primops.memory{1} = pointSubAssign_memory_footprint memory p1_addr
      )
    ].
    proof.
    proc.
      
