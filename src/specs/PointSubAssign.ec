pragma Goals:printall.

require import Array.
require        Constants.
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
}.

lemma usr_pointSubAssign_extracted_matches_low :
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
