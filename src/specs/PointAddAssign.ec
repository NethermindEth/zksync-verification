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

lemma pointAddAssign_low_pspec_revert:
    phoare [ PointAddAssign.low :
    Primops.reverted ==>
    Primops.reverted
    ] = 1%r.
    proof.
      proc.
      inline Primops.mload Primops.mstore Primops.gas.
      sp.
      inline*. wp. skip. by progress.
    qed.
    

lemma pointAddAssign_low_equiv_into_dest :
equiv [
    PointAddAssign.low ~ PointAddIntoDest.low:
      arg{2} = (arg{1}.`1, arg{1}.`2, arg{1}.`1) /\
      ={glob PointAddAssign} ==>
      (Primops.reverted{1} /\ Primops.reverted{2}) \/
      ={glob PointAddAssign}
    ].
    proof.
      proc.
      seq 9 9: (={glob PointAddAssign} /\ ={_13} /\ p1{1} = dest{2}).
      inline Primops.mload Primops.mstore Primops.gas. sp. skip. by progress.
      seq 1 1: (#pre /\ ={_14}).
      inline*. wp. skip. by progress.
      if. by progress.
      inline*. wp. skip. by progress.
      skip. by progress.
  qed.

lemma pointAddAssign_low_equiv_into_dest_mid (mem_0: mem) (p1_addr p2_addr: uint256) (p1 p2: int*int) :
equiv [
    PointAddAssign.low ~ PointAddIntoDest.mid:
      arg{1} = (p1_addr, p2_addr) /\
    W256.of_int 128 <= p1_addr /\ W256.of_int 64 <= -p1_addr /\
    W256.of_int 128 <= p2_addr /\ W256.of_int 64 <= -p2_addr /\
    0 <= p1.`1 < p /\ 0 <= p1.`2 < p /\ 0 <= p2.`1 < p /\ 0 <= p2.`2 < p /\
    Primops.memory{1} = mem_0 /\
    W256.to_uint (load mem_0 p1_addr) = p1.`1 /\
    W256.to_uint (load mem_0 (p1_addr + W256.of_int 32)) = p1.`2 /\
    W256.to_uint (load mem_0 p2_addr) = p2.`1 /\
    W256.to_uint (load mem_0 (p2_addr + W256.of_int 32)) = p2.`2 /\
      arg{2} = (p1.`1, p1.`2, p2.`1, p2.`2) /\
    !Primops.reverted{1} ==>
      (
        ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int p1.`1, W256.of_int p1.`2) (W256.of_int p2.`1, W256.of_int p2.`2) /\
        exists (x y: F),
        ecAdd_precompile (ZModField.inzmod p1.`1) (ZModField.inzmod p1.`2) (ZModField.inzmod p2.`1) (ZModField.inzmod p2.`2) = Some (x,y) /\
        res{2} = Some (ZModField.asint x, ZModField.asint y) /\
        Primops.memory{1} = pointAddIntoDest_memory_footprint mem_0 p1_addr p1 p2 (x,y) /\
        !Primops.reverted{1}
      ) \/
      (
        !ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int p1.`1, W256.of_int p1.`2) (W256.of_int p2.`1, W256.of_int p2.`2) /\
        res{2} = None /\
        Primops.reverted{1}
      )
    ].
    proof.
      transitivity PointAddIntoDest.low
    (
      arg{2} = (arg{1}.`1, arg{1}.`2, arg{1}.`1) /\
      arg{1} = (p1_addr, p2_addr) /\
      ={glob PointAddAssign} ==>
      (Primops.reverted{1} /\ Primops.reverted{2}) \/
      ={glob PointAddAssign}
    )
    (
      arg{1} = (p1_addr, p2_addr, p1_addr) /\
      W256.of_int 128 <= p1_addr /\ W256.of_int 64 <= -p1_addr /\
      W256.of_int 128 <= p2_addr /\ W256.of_int 64 <= -p2_addr /\
      0 <= p1.`1 < p /\ 0 <= p1.`2 < p /\ 0 <= p2.`1 < p /\ 0 <= p2.`2 < p /\
      Primops.memory{1} = mem_0 /\
      W256.to_uint (load mem_0 p1_addr) = p1.`1 /\
      W256.to_uint (load mem_0 (p1_addr + W256.of_int 32)) = p1.`2 /\
      W256.to_uint (load mem_0 p2_addr) = p2.`1 /\
      W256.to_uint (load mem_0 (p2_addr + W256.of_int 32)) = p2.`2 /\
      arg{2} = (p1.`1, p1.`2, p2.`1, p2.`2) /\
      !Primops.reverted{1} ==>
      (
        ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int p1.`1, W256.of_int p1.`2) (W256.of_int p2.`1, W256.of_int p2.`2) /\
             exists (x y: F),
        ecAdd_precompile (ZModField.inzmod p1.`1) (ZModField.inzmod p1.`2) (ZModField.inzmod p2.`1) (ZModField.inzmod p2.`2) = Some (x,y) /\
        res{2} = Some (ZModField.asint x, ZModField.asint y) /\
        Primops.memory{1} = pointAddIntoDest_memory_footprint mem_0 p1_addr p1 p2 (x,y) /\
        !Primops.reverted{1}
      ) \/
      (
        !ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int p1.`1, W256.of_int p1.`2) (W256.of_int p2.`1, W256.of_int p2.`2) /\
        res{2} = None /\
        Primops.reverted{1}
      )
    ).
        progress.
        exists (Primops.memory{1}) (Primops.reverted{1}) (p1_addr, p2_addr, p1_addr).
        by progress.
        progress.
        smt ().
        conseq (_ :
      arg{2} = (arg{1}.`1, arg{1}.`2, arg{1}.`1) /\
      ={glob PointAddAssign} ==>
      (Primops.reverted{1} /\ Primops.reverted{2}) \/
      ={glob PointAddAssign}
    ).
        by progress.
        exact pointAddAssign_low_equiv_into_dest.
        exact pointAddIntoDest_low_equiv_mid.
    qed.
    
