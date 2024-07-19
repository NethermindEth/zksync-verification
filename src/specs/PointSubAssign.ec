pragma Goals:printall.

require import Array.
require        Constants.
require import EllipticCurve.
require import Logic.
require import Memory.
require import PointAddAssign.
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

  proc mid(p1: int*int, p2: int*int): (int*int) option = {
    var neg_p2, neg_p2_F, neg_p2_opt, p1_F, ret;
    neg_p2_opt <@ PointNegate.mid(p2);
    if (neg_p2_opt = None) {
      ret <- None;
    } else {
      neg_p2 <- odflt (0,0) neg_p2_opt;
      ret <@ PointAddAssign.mid(p1, neg_p2);
    }
    return (omap from_point ret);
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
      
