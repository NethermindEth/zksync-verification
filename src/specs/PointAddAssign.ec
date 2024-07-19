pragma Goals:printall.

require import Array.
require import EllipticCurve.
require import Logic.
require import Memory.
require import PointAddIntoDest.
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

module PointAddAssign = {
  proc low(p1, p2) = {
    var _1, _5, _6, _9, _13, _14;
    _1 <@ Primops.mload(p1);
    Primops.mstore(W256.zero, _1);
    _5 <@ Primops.mload(p1 + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    _6 <@ Primops.mload(p2);
    Primops.mstore(W256.of_int 64, _6);
    _9 <@ Primops.mload(p2 + W256.of_int 32);
    Primops.mstore(W256.of_int 96, _9);
    _13 <@ Primops.gas();
    _14 <@ Primops.staticcall(_13, W256.of_int 6, W256.zero, W256.of_int 128, p1, W256.of_int 64);
    if ((bool_of_uint256 (PurePrimops.iszero _14)))
    {
      RevertWithMessage.low(W256.of_int 28, (W256.of_int STRING (*pointAddAssign: ecAdd failed*)));
    }
  }

  proc mid(p1: int*int, p2: int*int): (int*int) option = {
    var p1_F, p2_F, result;
    p1_F <- to_point p1;
    p2_F <- to_point p2;
    result <- ecAdd_precompile p1_F.`1 p1_F.`2 p2_F.`1 p2_F.`2;
    return (omap from_point result);
  }
}.

lemma pointAddAssign_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_pointAddAssign ~ PointAddAssign.low :
      ={arg, glob PointAddAssign} ==>
      ={res, glob PointAddAssign}
    ].
proof.
  proc.  
  seq 22 9: (#pre /\ ={_13} /\ _12{1} = W256.of_int 6 /\ _2{1} = W256.zero /\ _11{1} = W256.of_int 128 /\ usr_p1{1} = p1{2} /\ _7{1} = W256.of_int 64).
  inline*. wp. skip. by progress.
  seq 1 1: (#pre /\ tmp77{1} = _14{2}).
  inline*. wp. skip. by progress.
  inline*. wp. skip. by progress.
qed.

lemma pointAddAssign_equiv_into_dest :
equiv [
    PointAddAssign.low ~ PointAddIntoDest.low:
      arg{2} = (arg{1}.`1, arg{1}.`2, arg{1}.`1) /\
      ={glob PointAddAssign} ==>
      ={glob PointAddAssign}
    ].
    proof.
      proc.
      seq 9 9: (={glob PointAddAssign} /\ ={_13}).
      inline Primops.mload Primops.mstore Primops.gas. sp. skip. by progress.
      seq 1 1: (={glob PointAddAssign} /\ ={_14}).
      inline*. wp. skip. progress.
      
    

import ConcretePrimops.

op pointAddAssign_memory_footprint (mem_0: mem) (p1_address p2_address) =
  let p1_x = load mem_0 p1_address in
  let p1_y = load mem_0 (p1_address + W256.of_int 32) in
  let p2_x = load mem_0 p2_address in
  let p2_y = load mem_0 (p2_address + W256.of_int 32) in
  let mem_1 = store mem_0 W256.zero (ecAdd_precompile_unsafe_cast (p1_x, p1_y) (p2_x, p2_y)).`1 in
  let mem_2 = store mem_1 (W256.of_int 32) (ecAdd_precompile_unsafe_cast (p1_x, p1_y) (p2_x, p2_y)).`2 in
  let mem_3 = store mem_2 (W256.of_int 64) p2_x in
  store mem_3 (W256.of_int 96) p2_y.

pred low_inputs_valid (p1_address p2_address: uint256) =
    W256.of_int 128 <= p1_address /\ W256.of_int 128 <= -p1_address /\
    W256.of_int 128 <= p2_address /\ W256.of_int 128 <= -p2_address.
pred mid_inputs_valid (p1 p2: (int*int)) =
    0 <= p1.`1 < p /\ 0 <= p1.`2 < p /\ 0 <= p2.`1 < p /\ 0 <= p2.`2 < p.
pred mid_inputs_in_memory (memory: mem) (p1_address p2_address: uint256) (p1 p2: (int*int)) =
    W256.to_uint (load memory p1_address) = p1.`1 /\
    W256.to_uint (load memory (p1_address + W256.of_int 32)) = p1.`2 /\
    W256.to_uint (load memory p2_address) = p2.`1 /\
    W256.to_uint (load memory (p2_address + W256.of_int 32)) = p2.`2.

lemma pointAddAssign_low_equiv_mid (memory: mem) (p1_address p2_address: uint256) (p1 p2: (int*int)) :
    equiv [
      PointAddAssign.low ~ PointAddAssign.mid :
      low_inputs_valid p1_address p2_address /\
      mid_inputs_valid p1 p2 /\
      Primops.memory{1} = memory /\
      mid_inputs_in_memory memory p1_address p2_address p1 p2 /\
      arg{1} = (p1_address, p2_address) /\
      arg{2} = (p1, p2) /\
      !Primops.reverted{1} ==>
      (res{2} = None /\ Primops.reverted{1}) \/
      (
        exists p, res{2} = Some p /\
        !Primops.reverted{1} /\
        Primops.memory{1} = pointAddAssign_memory_footprint memory p1_address p2_address
      )
    ].
    proof.
      proc.
      (* Initial memory setup before static_call *)
      pose mem_1 := store memory W256.zero (load memory p1_address).
      pose mem_2 := store mem_1 (W256.of_int 32) (load memory (p1_address + W256.of_int 32)).
      pose mem_3 := store mem_2 (W256.of_int 64) (load memory p2_address).
      pose mem_4 := store mem_3 (W256.of_int 96) (load memory (p2_address + W256.of_int 32)).
      seq 8 0 : (
        low_inputs_valid p1_address p2_address /\
        mid_inputs_valid p1 p2 /\
        Primops.memory{1} = mem_4 /\
        !Primops.reverted{1}
      ).
      inline Primops.mload.
      call{1} (mstore_pspec mem_3 (W256.of_int 96) (load memory (p2_address + W256.of_int 32))). wp. 
      call{1} (mstore_pspec mem_2 (W256.of_int 64) (load memory p2_address)). wp.
      call{1} (mstore_pspec mem_1 (W256.of_int 32) (load memory (p1_address + W256.of_int 32))). wp. 
      call{1} (mstore_pspec memory W256.zero (load memory p1_address)). wp.
      skip. rewrite /low_inputs_valid. progress.
      rewrite load_store_diff; [smt (@W256 @Utils) | smt (@W256 @Utils) | reflexivity].
      rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
      rewrite /mem_1. rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils). reflexivity.
      rewrite load_store_diff. rewrite uint256_le_of_le. simplify. rewrite - addrA.
      have H_offset: ((W256.of_int 32) - (W256.of_int 64)) = - W256.of_int 32 by smt.
      rewrite H_offset. rewrite uint256_cast_sub. rewrite W256.of_uintK W256.of_uintK.
          rewrite pmod_small. rewrite pmod_small. rewrite pmod_small. smt (@W256).
          progress. smt (@W256 @Utils). smt.
          progress. smt (@W256 @Utils). smt.
      rewrite pmod_small. progress. smt (@W256 @Utils). smt. smt (pmod_small @W256 @Utils).

      









      
