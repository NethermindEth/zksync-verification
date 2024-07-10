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

module PointMulAndAddIntoDest = {
  proc low(usr_point, usr_s, usr_dest) =
  {
    var _1, _5, _9, usr_success, _10, _12, _15, _16, tmp87;
    _1 <@ Primops.mload(usr_point);
    Primops.mstore(W256.zero, _1);
    _5 <@ Primops.mload(usr_point + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    Primops.mstore(W256.of_int 64, usr_s);
    _9 <@ Primops.gas();
    usr_success <@ Primops.staticcall(_9, W256.of_int 7, W256.zero, W256.of_int 96, W256.zero, W256.of_int 64);
    _10 <@ Primops.mload(usr_dest);
    Primops.mstore(W256.of_int 64, _10);
    _12 <@ Primops.mload(usr_dest + W256.of_int 32);
    Primops.mstore(W256.of_int 96, _12);
    _15 <@ Primops.gas();
    _16 <@ Primops.staticcall(_15, W256.of_int 6, W256.zero, W256.of_int 128, usr_dest, W256.of_int 64);
    usr_success <- (PurePrimops.bit_and usr_success _16);
    if ((bool_of_uint256 (PurePrimops.iszero usr_success)))
      {
      tmp87 <@ Verifier.usr_revertWithMessage(W256.of_int 22, W256.of_int STRING);
      }
  }
}.

lemma usr_pointMulAndAddIntoDest_actual_matches_low (x y : uint256) : equiv [
    Verifier.usr_pointMulAndAddIntoDest ~ PointMulAndAddIntoDest.low :
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
  seq 20 9: (#pre /\ ={_1} /\ _2{1} = W256.zero /\ _3{1} = W256.of_int 32 /\  _4{1} = usr_point{1} + _3{1} /\
            _6{1} = W256.of_int 64 /\ _7{1} = W256.of_int 96 /\ _8{1} = W256.of_int 7 /\ ={_5, _9, usr_success, _10}).
  inline*. wp. skip. progress. sp.
  seq 9 4: (#pre /\ ={_12} /\ _13{1} = W256.of_int 128 /\ _14{1} = W256.of_int 6 /\ ={_15, _16}).
  inline*. wp. skip. progress.
  inline*. wp. skip. progress.
qed.