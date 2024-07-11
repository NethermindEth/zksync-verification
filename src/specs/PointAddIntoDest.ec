pragma Goals:printall.

require import Array.
require import EllipticCurve.
require import Logic.
require import Memory.
require import PurePrimops.
require import Real.
require import RevertWithMessage.
require import UInt256.
require import Utils.
require import YulPrimops.
require import Verifier.

module PointAddIntoDest = {
  proc low(p1, p2, dest) =
  {
    var _1, _5, _6, _9, _13, _14;
    _1 <@ Primops.mload(p1);
    Primops.mstore(W256.of_int 0, _1);
    _5 <@ Primops.mload(p1 + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    _6 <@ Primops.mload(p2);
    Primops.mstore(W256.of_int 64, _6);
    _9 <@ Primops.mload(p2 + W256.of_int 32);
    Primops.mstore(W256.of_int 96, _9);
    _13 <@ Primops.gas();
    _14 <@ Primops.staticcall(_13, W256.of_int 6, W256.zero, W256.of_int 128, dest, W256.of_int 64);
    if ((bool_of_uint256 (PurePrimops.iszero _14)))
    {
      RevertWithMessage.low((W256.of_int 30), (W256.of_int STRING (*pointAddIntoDest: ecAdd failed*)));
    }
  }
}.

lemma pointAddIntoDest_extracted_equiv_low : equiv [
    Verifier_1261.usr_pointAddIntoDest ~ PointAddIntoDest.low :
      ={arg, glob PointAddIntoDest} ==>
      ={res, glob PointAddIntoDest}
    ].
proof.
  proc.
  seq 24 10: (#pre /\ ={_14}).
  inline*. wp. skip. by progress.
  inline*. wp. skip. by progress.
qed.
