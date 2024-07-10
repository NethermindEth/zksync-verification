require        Constants.
require import PointMulAndAddIntoDest.
require import PointNegate.
require import PointSubAssign.
require import PurePrimops.
require import RevertWithMessage.
require import Utils.
require import Verifier.
require        VerifierConsts.
require import YulPrimops.

module FinalPairing = {
  proc low(): unit = {
    var u, z, _5, zOmega, _11, _14, _17, uu, _20, _23, _33, _35, _47, success, _50;
    u <@ Primops.mload(W256.of_int 4032);
    z <@ Primops.mload(W256.of_int 4064);
    _5 <@ Primops.mload(W256.of_int 4064);
    zOmega <- (PurePrimops.mulmod _5 (W256.of_int Constants.OMEGA) (W256.of_int Constants.R));
    PointSubAssign.low(W256.of_int 4736, W256.of_int 4672);
    PointMulAndAddIntoDest.low(W256.of_int 3136, z, W256.of_int 4736);
    PointMulAndAddIntoDest.low(W256.of_int 3200, (PurePrimops.mulmod zOmega u (W256.of_int Constants.R)), W256.of_int 4736);
    _11 <@ Primops.mload(W256.of_int 3136);
    Primops.mstore(W256.of_int 4864, _11);
    _14 <@ Primops.mload(W256.of_int 3168);
    Primops.mstore(W256.of_int 4896, _14);
    PointMulAndAddIntoDest.low(W256.of_int 3200, u, W256.of_int 4864);
    PointNegate.low(W256.of_int 4864);
    _17 <@ Primops.mload(W256.of_int 1792);
    if ((bool_of_uint256 _17))
    {
      uu <- (PurePrimops.mulmod u u (W256.of_int Constants.R));
      PointMulAndAddIntoDest.low(W256.of_int 3264, uu, W256.of_int 4736);
      PointMulAndAddIntoDest.low(W256.of_int 3328, uu, W256.of_int 4864);
    }
    
    _20 <@ Primops.mload(W256.of_int 4736);
    Primops.mstore(W256.zero, _20);
    _23 <@ Primops.mload(W256.of_int 4768);
    Primops.mstore(W256.of_int 32, _23);
    Primops.mstore(W256.of_int 64, VerifierConsts.G2_ELEMENTS_0_X1);
    Primops.mstore(W256.of_int 96, VerifierConsts.G2_ELEMENTS_0_X2);
    Primops.mstore(W256.of_int 128, VerifierConsts.G2_ELEMENTS_0_Y1);
    Primops.mstore(W256.of_int 160, VerifierConsts.G2_ELEMENTS_0_Y2);
    _33 <@ Primops.mload(W256.of_int 4864);
    Primops.mstore(W256.of_int 192, _33);
    _35 <@ Primops.mload(W256.of_int 4896);
    Primops.mstore(W256.of_int 224, _35);
    Primops.mstore(W256.of_int 256, VerifierConsts.G2_ELEMENTS_1_X1);
    Primops.mstore(W256.of_int 288, VerifierConsts.G2_ELEMENTS_1_X2);
    Primops.mstore(W256.of_int 320, VerifierConsts.G2_ELEMENTS_1_Y1);
    Primops.mstore(W256.of_int 352, VerifierConsts.G2_ELEMENTS_1_Y2);
    _47 <@ Primops.gas();
    success <@ Primops.staticcall(_47, W256.of_int 8, W256.zero, W256.of_int 384, W256.zero, W256.of_int 32);
    if ((bool_of_uint256 (PurePrimops.iszero success)))
    {
      RevertWithMessage.low(W256.of_int 32, W256.of_int STRING (*finalPairing: precompile failure*));
    }
    
    _50 <@ Primops.mload(W256.zero);
    if ((bool_of_uint256 (PurePrimops.iszero _50)))
    {
      RevertWithMessage.low(W256.of_int 29, W256.of_int STRING (*finalPairing: pairing failure*));
    }
  }
}.

lemma finalPairing_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_finalPairing ~ FinalPairing.low:
      ={arg, glob FinalPairing} ==>
      ={res, glob FinalPairing}
    ].
    proof.
      proc.
      inline Primops.mstore Primops.mload.
      seq 39 22 : (#pre /\ usr_u{1} = u{2} /\ _3{1} = W256.of_int Constants.R /\ _7{1} = W256.of_int 4736 /\ _12{1} = W256.of_int 4864 /\ _15{1} = W256.of_int 4896).
      call pointNegate_extracted_equiv_low.
      call pointMulAndAddIntoDest_extracted_equiv_low.
      wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointSubAssign_extracted_equiv_low. wp.
      skip.
      rewrite /Constants.R /Constants.OMEGA.
      by progress.
      seq 76 47: (#pre /\ _21{1} = W256.zero /\ _24{1} = W256.of_int 32 /\ _46{1} = W256.of_int 8).
      sp.
      if. by progress.
      wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      skip. by progress.
      wp. skip. by progress.
      wp.
      seq 4 2: (#pre /\ usr_success{1} = success{2}).
      inline*.
      do 3! (rcondf{2} 8; first progress; first wp; first skip; first progress; first exact neq_small).
      do 3! (rcondf{1} 9; first progress; first wp; first skip; first progress; first exact neq_small).
      rcondt{1} 9. progress. wp. skip. by progress.
      rcondt{2} 8. progress. wp. skip. by progress.
      wp. skip. by progress.
      sp.
      if. by progress.
      seq 2 1: #pre. sp. call revertWithMessage_extracted_equiv_low. skip. by progress.
      sp.
      if. by progress.
      sp.
      call revertWithMessage_extracted_equiv_low. skip. by progress.
      skip. by progress.
      sp.
      if. by progress.
      sp.
      call revertWithMessage_extracted_equiv_low. skip. by progress.
      skip. by progress.
    qed.
