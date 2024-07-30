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
