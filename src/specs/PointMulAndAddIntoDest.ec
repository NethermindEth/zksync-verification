pragma Goals:printall.

require import Array.
require import EllipticCurve.
require import Logic.
require import Memory.
require import PointAddIntoDest.
require import PointMulIntoDest.
require import PurePrimops.
require import Real.
require import RevertWithMessage.
require import UInt256.
require import Utils.
require import YulPrimops.
require import Verifier.

import MemoryMap.

module PointMulAndAddIntoDest = {
  proc low(point, s, dest) =
  {
    var _1, _5, _9, success, _10, _12, _15, _16;
    _1 <@ Primops.mload(point);
    Primops.mstore(W256.zero, _1);
    _5 <@ Primops.mload(point + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    Primops.mstore(W256.of_int 64, s);
    _9 <@ Primops.gas();
    success <@ Primops.staticcall(_9, W256.of_int 7, W256.zero, W256.of_int 96, W256.zero, W256.of_int 64);
    _10 <@ Primops.mload(dest);
    Primops.mstore(W256.of_int 64, _10);
    _12 <@ Primops.mload(dest + W256.of_int 32);
    Primops.mstore(W256.of_int 96, _12);
    _15 <@ Primops.gas();
    _16 <@ Primops.staticcall(_15, W256.of_int 6, W256.zero, W256.of_int 128, dest, W256.of_int 64);
    success <- (PurePrimops.bit_and success _16);
    if ((bool_of_uint256 (PurePrimops.iszero success)))
    {
      RevertWithMessage.low(W256.of_int 22, W256.of_int STRING);
    }
  }

  proc low'(point, s, dest) = {
    PointMulIntoDest.low(point, s, W256.zero);
    PointAddIntoDest.low(W256.zero, dest, dest);
  }
}.

lemma pointMulAndAddIntoDest_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_pointMulAndAddIntoDest ~ PointMulAndAddIntoDest.low :
      ={arg, glob PointMulAndAddIntoDest} ==>
      ={res, glob PointMulAndAddIntoDest}
    ].
proof.
  proc.
  seq 20 9: (#pre /\ ={_1} /\ _2{1} = W256.zero /\ _3{1} = W256.of_int 32 /\  _4{1} = usr_point{1} + _3{1} /\
            _6{1} = W256.of_int 64 /\ _7{1} = W256.of_int 96 /\ _8{1} = W256.of_int 7 /\ ={_5, _9, _10} /\ usr_success{1} = success{2}).
  inline*. wp. skip. by progress.
  sp.
  seq 9 4: (#pre /\ ={_12} /\ _13{1} = W256.of_int 128 /\ _14{1} = W256.of_int 6 /\ ={_15, _16}).
  inline*. wp. skip. by progress.
  inline*. wp. skip. by progress.
qed.

lemma pointMulAndAddIntoDest_low_equiv_low':
    equiv [
      PointMulAndAddIntoDest.low ~ PointMulAndAddIntoDest.low' :
      ={arg, glob PointMulAndAddIntoDest} ==>
      (
        (!Primops.reverted{1} /\ !Primops.reverted{2}) \/
        ={res, glob PointMulAndAddIntoDest}
      )
    ].
    proof.
      proc.
      inline PointMulIntoDest.low.
      seq 6 9: (#pre /\ ={_9} /\ ={dest} /\ dest0{2} = W256.zero). (*lead up to the first static call *)
      sp.
      inline*. wp. skip. by progress.
      seq 1 1: (#pre /\ success{1} = _10{2}).
      exists* Primops.memory{1}, Primops.memory{2}.
      elim*=> memory1 memory2.
      call{1} (
        ConcretePrimops.staticcall_ec_mul_pspec
        memory1
        ((load memory1 W256.zero),
        (load memory1 (W256.of_int 32)))
        ((load memory1 (W256.of_int 64)),
        (load memory1 (W256.of_int 96)))
        W256.zero
        (W256.of_int 64)
      ).
      call{2} (
        ConcretePrimops.staticcall_ec_mul_pspec
        memory2
        ((load memory2 W256.zero),
        (load memory2 (W256.of_int 32)))
        ((load memory2 (W256.of_int 64)),
        (load memory2 (W256.of_int 96)))
        W256.zero
        (W256.of_int 64)
      ).
      skip. progress.
          inline Primops.staticcall.
      sp.
      rcondf{1} 1. progress. skip. progress. smt (@W256 @Utils).
      rcondf{2} 1. progress. skip. progress. smt (@W256 @Utils).
      rcondf{1} 1. progress. skip. progress. smt (@W256 @Utils).
      rcondf{2} 1. progress. skip. progress. smt (@W256 @Utils).
      rcondt{1} 1. by progress.
      rcondt{2} 1. by progress.
      rcondt{1} 1. by progress.
      rcondt{2} 1. by progress.
      wp. sim. progress.
      
