require        Constants.
require import PointMulAndAddIntoDest.
require import PointNegate.
require import PointSubAssign.
require import PurePrimops.
require import RevertWithMessage.
require import Utils.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module FinalPairing = {
  proc low(): unit = {
    var u, z, _5, zOmega, _11, _14, _17, uu, _20, _23, _33, _35, _47, success, _50;
    u <@ Primops.mload(STATE_U_SLOT);
    z <@ Primops.mload(STATE_Z_SLOT);
    _5 <@ Primops.mload(STATE_Z_SLOT);
    zOmega <- (PurePrimops.mulmod _5 OMEGA R_MOD);
    PointSubAssign.low(PAIRING_PAIR_WITH_GENERATOR_X_SLOT, PAIRING_BUFFER_POINT_X_SLOT);
    PointMulAndAddIntoDest.low(PROOF_OPENING_PROOF_AT_Z_X_SLOT, z, PAIRING_PAIR_WITH_GENERATOR_X_SLOT);
    PointMulAndAddIntoDest.low(PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT, (PurePrimops.mulmod zOmega u R_MOD), PAIRING_PAIR_WITH_GENERATOR_X_SLOT);
    _11 <@ Primops.mload(PROOF_OPENING_PROOF_AT_Z_X_SLOT);
    Primops.mstore(PAIRING_PAIR_WITH_X_X_SLOT, _11);
    _14 <@ Primops.mload(PROOF_OPENING_PROOF_AT_Z_Y_SLOT);
    Primops.mstore(PAIRING_PAIR_WITH_X_Y_SLOT, _14);
    PointMulAndAddIntoDest.low(PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT, u, PAIRING_PAIR_WITH_X_X_SLOT);
    PointNegate.low(PAIRING_PAIR_WITH_X_X_SLOT);
    _17 <@ Primops.mload(VK_RECURSIVE_FLAG_SLOT);
    if (bool_of_uint256 _17)
    {
      uu <- (PurePrimops.mulmod u u R_MOD);
      PointMulAndAddIntoDest.low(PROOF_RECURSIVE_PART_P1_X_SLOT, uu, PAIRING_PAIR_WITH_GENERATOR_X_SLOT);
      PointMulAndAddIntoDest.low(PROOF_RECURSIVE_PART_P2_X_SLOT, uu, PAIRING_PAIR_WITH_X_X_SLOT);
    }
    
    _20 <@ Primops.mload(PAIRING_PAIR_WITH_GENERATOR_X_SLOT);
    Primops.mstore(W256.zero, _20);
    _23 <@ Primops.mload(PAIRING_PAIR_WITH_GENERATOR_Y_SLOT);
    Primops.mstore(W256.of_int 32, _23);
    Primops.mstore(W256.of_int 64, VerifierConsts.G2_ELEMENTS_0_X1);
    Primops.mstore(W256.of_int 96, VerifierConsts.G2_ELEMENTS_0_X2);
    Primops.mstore(W256.of_int 128, VerifierConsts.G2_ELEMENTS_0_Y1);
    Primops.mstore(W256.of_int 160, VerifierConsts.G2_ELEMENTS_0_Y2);
    _33 <@ Primops.mload(PAIRING_PAIR_WITH_X_X_SLOT);
    Primops.mstore(W256.of_int 192, _33);
    _35 <@ Primops.mload(PAIRING_PAIR_WITH_X_Y_SLOT);
    Primops.mstore(W256.of_int 224, _35);
    Primops.mstore(W256.of_int 256, VerifierConsts.G2_ELEMENTS_1_X1);
    Primops.mstore(W256.of_int 288, VerifierConsts.G2_ELEMENTS_1_X2);
    Primops.mstore(W256.of_int 320, VerifierConsts.G2_ELEMENTS_1_Y1);
    Primops.mstore(W256.of_int 352, VerifierConsts.G2_ELEMENTS_1_Y2);
    _47 <@ Primops.gas();
    success <@ Primops.staticcall(_47, W256.of_int 8, W256.zero, W256.of_int 384, W256.zero, W256.of_int 32);
    if (bool_of_uint256 (PurePrimops.iszero success))
    {
      RevertWithMessage.low(W256.of_int 32, W256.of_int STRING (*finalPairing: precompile failure*));
    }
    
    _50 <@ Primops.mload(W256.zero);
    if (bool_of_uint256 (PurePrimops.iszero _50))
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
      seq 39 22 : (#pre /\ usr_u{1} = u{2} /\ _3{1} = R_MOD /\ _7{1} = PAIRING_PAIR_WITH_GENERATOR_X_SLOT /\ _12{1} = PAIRING_PAIR_WITH_X_X_SLOT /\ _15{1} = PAIRING_PAIR_WITH_X_Y_SLOT).
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
