pragma Goals:printall.

require import Array.
require import EllipticCurve.
require import Logic.
require import Memory.
require import PurePrimops.
require import Real.
require import UInt256.
require import Utils.
require import YulPrimops.
require import Verifier.

import MemoryMap.

module PointSubAssign = {
  proc low(usr_p1, usr_p2) =
  {
    var _1, _5, _6, _9, _15, _16, tmp71;
    _1 <@ Primops.mload(usr_p1);
    Primops.mstore(W256.zero, _1);
    _5 <@ Primops.mload(usr_p1 + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    _6 <@ Primops.mload(usr_p2);
    Primops.mstore(W256.of_int 64, _6);
    _9  <@ Primops.mload(usr_p2 + W256.of_int 32);
    Primops.mstore(W256.of_int 96, W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583 - _9);
    _15 <@ Primops.gas();
    _16 <@ Primops.staticcall(_15, W256.of_int 6, W256.zero, W256.of_int 128, usr_p1, W256.of_int 64);
    if ((bool_of_uint256 (PurePrimops.iszero _16)))
      {
      tmp71 <@ Verifier.usr_revertWithMessage(W256.of_int 28, (W256.of_int STRING));
      }
  }
}.

lemma usr_pointSubAssign_actual_matches_low (x y : uint256) : equiv [
    Verifier.usr_pointSubAssign ~ PointSubAssign.low :
      ={Primops.memory} /\
      ={arg} /\
      ={Primops.reverted} /\
      !Primops.reverted{1}
      ==>
        (Primops.reverted{1} <=> Primops.reverted{2}) /\
        (!Primops.reverted{1}) =>
        forall (idx: uint256),
        Primops.memory{1}.[idx] =
        Primops.memory{2}.[idx]
      ].
proof.
  proc.
  seq 16 7: (#pre /\ ={_1} /\ _2{1} = W256.zero /\ _3{1} = W256.of_int 32 /\ _4{1} = usr_p1{1} + _3{1}
            /\ ={_5, _6, _9} /\ _7{1} = W256.of_int 64 /\ _8{1} = usr_p2{1} + _3{1}).
  inline*. wp. skip. progress. sp.
  seq 7 3: (#pre /\ _13{1} = W256.of_int 128 /\ _14{1} = W256.of_int 6 /\ ={_15, _16}).
  inline*. wp. skip. progress.
  inline*. wp. skip. progress.
qed.  