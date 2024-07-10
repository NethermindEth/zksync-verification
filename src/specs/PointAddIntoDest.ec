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

module PointAddIntoDest = {
  proc low(usr_p1, usr_p2, usr_dest) =
  {
    var _1, _5, _6, _9, _13, _14, tmp64;
    _1 <@ Primops.mload(usr_p1);
    Primops.mstore(W256.of_int 0, _1);
    _5 <@ Primops.mload(usr_p1 + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    _6 <@ Primops.mload(usr_p2);
    Primops.mstore(W256.of_int 64, _6);
    _9 <@ Primops.mload(usr_p2 + W256.of_int 32);
    Primops.mstore(W256.of_int 96, _9);
    _13 <@ Primops.gas();
    _14 <@ Primops.staticcall(_13, W256.of_int 6, W256.zero, W256.of_int 128, usr_dest, W256.of_int 64);
    if ((bool_of_uint256 (PurePrimops.iszero _14)))
      {
      tmp64 <@ Verifier.usr_revertWithMessage((W256.of_int 30), (W256.of_int STRING (*pointAddIntoDest: ecAdd failed*)));
      }
  }
}.

lemma usr_pointAddIntoDest_actual_matches_low (x y : uint256) : equiv [
    Verifier.usr_pointAddIntoDest ~ PointAddIntoDest.low :
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
  seq 24 10: (#pre /\ ={_1, _5, _6, _9, _13, _14} /\ _2{1} = W256.zero /\ _3{1} = W256.of_int 32 /\ _4{1} = usr_p1{1} + _3{1}
             /\ _7{1} = W256.of_int 64 /\ _8{1} = usr_p2{1} + _3{1} /\ _10{1} = W256.of_int 96 /\ _11{1} = W256.of_int 128
             /\ _12{1} = W256.of_int 6).
  inline*. wp. skip. progress.
  inline*. wp. skip. progress.
qed.
