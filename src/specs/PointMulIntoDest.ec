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

module PointMulIntoDest = {
  proc low(point, s, dest) =
  {
    var _1, _5,  _9, _10;
    _1 <@ Primops.mload(point);
    Primops.mstore(W256.zero, _1);
    _5 <@ Primops.mload(point + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    Primops.mstore(W256.of_int 64, s);
    _9 <@ Primops.gas();
    _10 <@ Primops.staticcall(_9, W256.of_int 7, W256.zero, W256.of_int 96, dest, W256.of_int 64);
    if (bool_of_uint256 (PurePrimops.iszero(_10)))
    {
      RevertWithMessage.low(W256.of_int 30, W256.zero);
    }
  }
}.

lemma usr_pointMulIntoDest_extracted_matches_low (x y : uint256) : equiv [
    Verifier_1261.usr_pointMulIntoDest ~ PointMulIntoDest.low :
      ={arg, glob PointMulIntoDest} ==>
      ={res, glob PointMulIntoDest}
    ].
proof.
  proc.
  seq 17 7: (#pre /\ ={_10}).
  inline*. wp. skip. by progress.
  inline*. wp. skip. by progress.
qed.
