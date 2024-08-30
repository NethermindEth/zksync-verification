pragma Goals:printall.

require        Constants.
require import Field.
require import PointMulAndAddIntoDest.
require import PointNegate.
require import PointSubAssign.
require import PurePrimops.
require import RevertWithMessage.
require import Utils.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

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

  proc mid(u: int, z: int, pairing_pair_with_generator: (int*int), pairing_buffer_point: (int*int), opening_proof_at_z: (int*int), opening_proof_at_z_omega: (int*int), vk_recursive_flag: bool, recursive_part_p1: (int*int), recursive_part_p2: (int*int)): bool = {
    var _5, zOmega, uu;
    var pairing_pair_with_x: (int*int);
    var pairing_pair_with_generator_opt, pairing_pair_with_x_opt: (int*int) option;
    var pairing_result: bool option;
    var failed: bool;
    failed <- false;
    _5 <- z;
    zOmega <- (_5 * Constants.OMEGA) %% Constants.R;

    pairing_pair_with_generator_opt <@ PointSubAssign.mid(pairing_pair_with_generator, pairing_buffer_point);
    failed <- failed \/ is_none pairing_pair_with_generator_opt;
    pairing_pair_with_generator <- odflt (0,0) pairing_pair_with_generator_opt;

    pairing_pair_with_generator_opt <@ PointMulAndAddIntoDest.mid(opening_proof_at_z.`1, opening_proof_at_z.`2, z, pairing_pair_with_generator.`1, pairing_pair_with_generator.`2);
    failed <- failed \/ is_none pairing_pair_with_generator_opt;
    pairing_pair_with_generator <- odflt (0,0) pairing_pair_with_generator_opt;

    pairing_pair_with_generator_opt <@ PointMulAndAddIntoDest.mid(opening_proof_at_z_omega.`1, opening_proof_at_z_omega.`2, (zOmega * u) %% Constants.R, pairing_pair_with_generator.`1, pairing_pair_with_generator.`2);
    failed <- failed \/ is_none pairing_pair_with_generator_opt;
    pairing_pair_with_generator <- odflt (0,0) pairing_pair_with_generator_opt;

    pairing_pair_with_x_opt <@ PointMulAndAddIntoDest.mid(opening_proof_at_z_omega.`1, opening_proof_at_z_omega.`2, u, opening_proof_at_z.`1, opening_proof_at_z.`2);
    failed <- failed \/ is_none pairing_pair_with_x_opt;
    pairing_pair_with_x <- odflt (0,0) pairing_pair_with_x_opt;

    pairing_pair_with_x_opt <@ PointNegate.mid(pairing_pair_with_x);
    failed <- failed \/ is_none pairing_pair_with_x_opt;
    pairing_pair_with_x <- odflt (0,0) pairing_pair_with_x_opt;

    if (vk_recursive_flag)
    {
      uu <- (u * u) %% Constants.R;
      pairing_pair_with_generator_opt <@ PointMulAndAddIntoDest.mid(recursive_part_p1.`1, recursive_part_p1.`2, uu, pairing_pair_with_generator.`1, pairing_pair_with_generator.`2);
      failed <- failed \/ is_none pairing_pair_with_generator_opt;
      pairing_pair_with_generator <- odflt (0,0) pairing_pair_with_generator_opt;

      pairing_pair_with_x_opt <@ PointMulAndAddIntoDest.mid(recursive_part_p2.`1, recursive_part_p2.`2, uu, pairing_pair_with_x.`1, pairing_pair_with_x.`2);
      failed <- failed \/ is_none pairing_pair_with_x_opt;
      pairing_pair_with_x <- odflt (0,0) pairing_pair_with_x_opt;
    }
    
    pairing_result <- ecPairing_precompile
      (
        (FieldQ.inF pairing_pair_with_generator.`1, FieldQ.inF pairing_pair_with_generator.`2),
        (
          (FieldQ.inF Constants.G2_ELEMENT_0.`1.`1, FieldQ.inF Constants.G2_ELEMENT_0.`1.`2),
          (FieldQ.inF Constants.G2_ELEMENT_0.`2.`1, FieldQ.inF Constants.G2_ELEMENT_0.`2.`2)
        )
      )
      (
        (FieldQ.inF pairing_pair_with_x.`1, FieldQ.inF pairing_pair_with_x.`2),
        (
          (FieldQ.inF Constants.G2_ELEMENT_1.`1.`1, FieldQ.inF Constants.G2_ELEMENT_1.`1.`2),
          (FieldQ.inF Constants.G2_ELEMENT_1.`2.`1, FieldQ.inF Constants.G2_ELEMENT_1.`2.`2)
        )
      );
    failed <- failed \/ !(odflt false pairing_result);

    return !failed;
  }

  proc high_encapsulated(u: FieldR.F, z: FieldR.F, pairing_pair_with_generator: g, pairing_buffer_point: g, opening_proof_at_z: g, opening_proof_at_z_omega: g, vk_recursive_flag: bool, recursive_part_p1: g, recursive_part_p2: g): bool = {
    var pairing_pair_with_x: g;

    pairing_pair_with_generator <@ PointSubAssign.high(pairing_pair_with_generator, pairing_buffer_point);

    pairing_pair_with_generator <@ PointMulAndAddIntoDest.high(opening_proof_at_z, z, pairing_pair_with_generator);

    pairing_pair_with_generator <@ PointMulAndAddIntoDest.high(opening_proof_at_z_omega, z * Constants.OMEGAFr * u, pairing_pair_with_generator);

    pairing_pair_with_x <@ PointMulAndAddIntoDest.high(opening_proof_at_z_omega, u, opening_proof_at_z);

    pairing_pair_with_x <@ PointNegate.high(pairing_pair_with_x);

    if (vk_recursive_flag)
    {
      pairing_pair_with_generator <@ PointMulAndAddIntoDest.high(recursive_part_p1, u * u, pairing_pair_with_generator);
      pairing_pair_with_x <@ PointMulAndAddIntoDest.high(recursive_part_p2, u * u  , pairing_pair_with_x);
    }

    return e (pairing_pair_with_generator + pairing_pair_with_x) (Constants.G2_ELEMENT_0_G + Constants.G2_ELEMENT_1_G) = G.e;
  }

  proc high(u: FieldR.F, z: FieldR.F, pairing_pair_with_generator: g, pairing_buffer_point: g, opening_proof_at_z: g, opening_proof_at_z_omega: g, vk_recursive_flag: bool, recursive_part_p1: g, recursive_part_p2: g): bool = {
    var pairing_pair_with_x: g;

    pairing_pair_with_generator <- pairing_pair_with_generator + (G.inv pairing_buffer_point);
    pairing_pair_with_generator <- (z *opening_proof_at_z) + pairing_pair_with_generator;
    pairing_pair_with_generator <- ((z * Constants.OMEGAFr * u) * opening_proof_at_z_omega) + pairing_pair_with_generator;
    pairing_pair_with_x <- (u *opening_proof_at_z_omega) + opening_proof_at_z;
    pairing_pair_with_x <- G.inv pairing_pair_with_x;

    if (vk_recursive_flag)
    {
      pairing_pair_with_generator <- ((u * u) *recursive_part_p1) + pairing_pair_with_generator;
      pairing_pair_with_x <- ((u * u) * recursive_part_p2) + pairing_pair_with_x;
    }

    return e (pairing_pair_with_generator + pairing_pair_with_x) (Constants.G2_ELEMENT_0_G + Constants.G2_ELEMENT_1_G) = G.e;
  }
}.

lemma finalPairing_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_finalPairing ~ FinalPairing.low:
      ={arg, glob FinalPairing} ==>
      ={res, glob FinalPairing}
    ].
    proof.
      admit.
      (*proc.
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
      seq 76 47: (#pre /\ _21{1} = W256.zero /\ _24{1} = W256.of_int 32 /\ _45{1} = (of_int 384)%W256 /\  _46{1} = W256.of_int 8).
      sp.
      if. by progress.
      wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      skip. by progress.
      wp. skip. by progress.
      wp.
      seq 4 2: (#pre /\ usr_success{1} = success{2}).
      seq 2 1: (#pre).
      inline*. wp. skip. by progress.
      exists* Primops.memory{1}.
      elim* => mem.
      seq 1 1 : (#pre /\ tmp430{1} = success{2}).
      progress.
      call{1} (ConcretePrimops.staticcall_ec_pairing_pspec mem (PurePrimops.mload mem W256.zero, PurePrimops.mload mem (W256.of_int 32))
         (PurePrimops.mload mem (W256.of_int 192), PurePrimops.mload mem (W256.of_int 224))
         ((PurePrimops.mload mem (W256.of_int 64), PurePrimops.mload mem (W256.of_int 96)), (PurePrimops.mload mem (W256.of_int 128), PurePrimops.mload mem (W256.of_int 160)))
         ((PurePrimops.mload mem (W256.of_int 256), PurePrimops.mload mem (W256.of_int 288)), (PurePrimops.mload mem (W256.of_int 320), PurePrimops.mload mem (W256.of_int 352)))
           W256.zero W256.zero).
      call{2} (ConcretePrimops.staticcall_ec_pairing_pspec mem (PurePrimops.mload mem W256.zero, PurePrimops.mload mem (W256.of_int 32))
         (PurePrimops.mload mem (W256.of_int 192), PurePrimops.mload mem (W256.of_int 224))
         ((PurePrimops.mload mem (W256.of_int 64), PurePrimops.mload mem (W256.of_int 96)), (PurePrimops.mload mem (W256.of_int 128), PurePrimops.mload mem (W256.of_int 160)))
         ((PurePrimops.mload mem (W256.of_int 256), PurePrimops.mload mem (W256.of_int 288)), (PurePrimops.mload mem (W256.of_int 320), PurePrimops.mload mem (W256.of_int 352)))
           W256.zero W256.zero).
           progress. skip. progress.
      case ((ConcretePrimops.staticcall_ec_pairing_should_succeed
       ((PurePrimops.mload Primops.memory{2} W256.zero)%PurePrimops,
        (PurePrimops.mload Primops.memory{2} ((of_int 32))%W256)%PurePrimops)
       ((PurePrimops.mload Primops.memory{2} ((of_int 192))%W256)%PurePrimops,
        (PurePrimops.mload Primops.memory{2} ((of_int 224))%W256)%PurePrimops)
       (((PurePrimops.mload Primops.memory{2} ((of_int 64))%W256)%PurePrimops,
         (PurePrimops.mload Primops.memory{2} ((of_int 96))%W256)%PurePrimops),
        ((PurePrimops.mload Primops.memory{2} ((of_int 128))%W256)%PurePrimops,
         (PurePrimops.mload Primops.memory{2} ((of_int 160))%W256)%PurePrimops))
       (((PurePrimops.mload Primops.memory{2} ((of_int 256))%W256)%PurePrimops,
         (PurePrimops.mload Primops.memory{2} ((of_int 288))%W256)%PurePrimops),
        ((PurePrimops.mload Primops.memory{2} ((of_int 320))%W256)%PurePrimops,
         (PurePrimops.mload Primops.memory{2} ((of_int 352))%W256)%PurePrimops)))%ConcretePrimops).
      progress. smt(). 

  
      progress. 
      inline*.
      do 3! (rcondf{2} 9; first progress; first wp; first skip; first progress; first exact neq_small).
      do 3! (rcondf{1} 10; first progress; first wp; first skip; first progress; first exact neq_small).
      rcondt{1} 10. progress. wp. skip. by progress.
      rcondt{2} 9. progress. wp. skip. by progress.
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
      skip. by progress.*)
    qed.

lemma finalPairing_low_equiv_mid:
    equiv [
      FinalPairing.low ~ FinalPairing.mid:
      !Primops.reverted{1} /\
      u{2} = W256.to_uint (load Primops.memory{1} STATE_U_SLOT) /\
      z{2} = W256.to_uint (load Primops.memory{1} STATE_Z_SLOT) /\
      pairing_pair_with_generator{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_GENERATOR_X_SLOT) /\
      pairing_pair_with_generator{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_GENERATOR_Y_SLOT) /\ 
      pairing_buffer_point{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_BUFFER_POINT_X_SLOT) /\
      pairing_buffer_point{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_BUFFER_POINT_Y_SLOT) /\
      opening_proof_at_z{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_X_SLOT) /\
      opening_proof_at_z{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_Y_SLOT) /\
      opening_proof_at_z_omega{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT) /\
      opening_proof_at_z_omega{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT) /\
      vk_recursive_flag{2} = bool_of_uint256 (load Primops.memory{1} VK_RECURSIVE_FLAG_SLOT) /\
      recursive_part_p1{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P1_X_SLOT) /\
      recursive_part_p1{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P1_Y_SLOT) /\
      recursive_part_p2{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P2_X_SLOT) /\
      recursive_part_p2{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P2_Y_SLOT) /\
      0 <= pairing_pair_with_generator{2}.`1 < FieldQ.p /\
      0 <= pairing_pair_with_generator{2}.`2 < FieldQ.p /\
      0 <= pairing_buffer_point{2}.`1 < FieldQ.p /\
      0 <= pairing_buffer_point{2}.`2 < FieldQ.p /\
      0 <= opening_proof_at_z{2}.`1 < FieldQ.p /\
      0 <= opening_proof_at_z{2}.`2 < FieldQ.p /\
      0 <= opening_proof_at_z_omega{2}.`1 < FieldQ.p /\
      0 <= opening_proof_at_z_omega{2}.`2 < FieldQ.p /\
      0 <= u{2} < FieldR.p /\
      0 <= z{2} < FieldR.p /\ (
        vk_recursive_flag{2} => (
          0 <= recursive_part_p1{2}.`1 < FieldQ.p /\
          0 <= recursive_part_p1{2}.`2 < FieldQ.p /\
          0 <= recursive_part_p2{2}.`1 < FieldQ.p /\
          0 <= recursive_part_p2{2}.`2 < FieldQ.p
        )
      ) ==>
      Primops.reverted{1} = !res{2}
    ].
    proof.
      proc.
      simplify.
      
      seq 5 6: (
        (Primops.reverted{1} /\ failed{2}) \/ (
          !Primops.reverted{1} /\ !failed{2} /\
          u{2} = W256.to_uint (load Primops.memory{1} STATE_U_SLOT) /\
          z{2} = W256.to_uint (load Primops.memory{1} STATE_Z_SLOT) /\
           pairing_pair_with_generator{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_GENERATOR_X_SLOT) /\
          pairing_pair_with_generator{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_GENERATOR_Y_SLOT) /\ 
          pairing_buffer_point{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_BUFFER_POINT_X_SLOT) /\
          pairing_buffer_point{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_BUFFER_POINT_Y_SLOT) /\
          opening_proof_at_z{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_X_SLOT) /\
          opening_proof_at_z{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_Y_SLOT) /\
          opening_proof_at_z_omega{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT) /\
          opening_proof_at_z_omega{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT) /\
          vk_recursive_flag{2} = bool_of_uint256 (load Primops.memory{1} VK_RECURSIVE_FLAG_SLOT) /\
          recursive_part_p1{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P1_X_SLOT) /\
          recursive_part_p1{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P1_Y_SLOT) /\
          recursive_part_p2{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P2_X_SLOT) /\
          recursive_part_p2{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P2_Y_SLOT) /\
          0 <= pairing_pair_with_generator{2}.`1 < FieldQ.p /\
          0 <= pairing_pair_with_generator{2}.`2 < FieldQ.p /\
          0 <= pairing_buffer_point{2}.`1 < FieldQ.p /\
          0 <= pairing_buffer_point{2}.`2 < FieldQ.p /\
          0 <= opening_proof_at_z{2}.`1 < FieldQ.p /\
          0 <= opening_proof_at_z{2}.`2 < FieldQ.p /\
          0 <= opening_proof_at_z_omega{2}.`1 < FieldQ.p /\
          0 <= opening_proof_at_z_omega{2}.`2 < FieldQ.p /\
          0 <= u{2} < FieldR.p /\
          0 <= z{2} < FieldR.p /\
          u{2} = W256.to_uint u{1} /\
          z{2} = W256.to_uint z{1} /\
          zOmega{2} = W256.to_uint zOmega{1} /\ (
            vk_recursive_flag{2} => (
              0 <= recursive_part_p1{2}.`1 < FieldQ.p /\
              0 <= recursive_part_p1{2}.`2 < FieldQ.p /\
              0 <= recursive_part_p2{2}.`1 < FieldQ.p /\
              0 <= recursive_part_p2{2}.`2 < FieldQ.p
            )
          )
        )
      ).
      inline Primops.mload. sp. wp.
      exists* Primops.memory{1}, pairing_pair_with_generator{2}, pairing_buffer_point{2}.
      elim*=> memory_l pairing_pair_with_generator_r pairing_buffer_point_r.
      call (pointSubAssign_low_equiv_mid_fixed memory_l PAIRING_PAIR_WITH_GENERATOR_X_SLOT PAIRING_BUFFER_POINT_X_SLOT pairing_pair_with_generator_r pairing_buffer_point_r).
      skip.
      progress.
      by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT W256.of_intN'; progress.
      by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT W256.of_intN'; progress.
      by rewrite H0; reflexivity.
      by rewrite H1; reflexivity.
      by rewrite H2; reflexivity.
      by rewrite H3; reflexivity.
      case H50.
        by progress; left; progress.
        progress.
          by rewrite /pointSubAssign_memory_footprint /STATE_U_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          reflexivity.
          by rewrite /pointSubAssign_memory_footprint /STATE_Z_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          reflexivity.
          by rewrite /pointSubAssign_memory_footprint /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          rewrite load_store_diff; [
            progress |
            progress |
            rewrite load_store_same W256.of_uintK pmod_small; progress;
            rewrite (int_lt_lt_trans _ Constants.Q); [assumption | rewrite /Constants.Q; progress];
            reflexivity
          ].
          by rewrite /pointSubAssign_memory_footprint /PAIRING_PAIR_WITH_GENERATOR_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_Y_SLOT;
          simplify;
          rewrite load_store_same W256.of_uintK pmod_small; progress;
          rewrite (int_lt_lt_trans _ Constants.Q); [assumption | rewrite /Constants.Q; progress];
          reflexivity.
          by rewrite /pointSubAssign_memory_footprint /PAIRING_BUFFER_POINT_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite /pointSubAssign_memory_footprint /PAIRING_BUFFER_POINT_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite /pointSubAssign_memory_footprint /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite /pointSubAssign_memory_footprint /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite /pointSubAssign_memory_footprint /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite /pointSubAssign_memory_footprint /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite /pointSubAssign_memory_footprint /VK_RECURSIVE_FLAG_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite /pointSubAssign_memory_footprint /PROOF_RECURSIVE_PART_P1_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite /pointSubAssign_memory_footprint /PROOF_RECURSIVE_PART_P1_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite /pointSubAssign_memory_footprint /PROOF_RECURSIVE_PART_P2_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite /pointSubAssign_memory_footprint /PROOF_RECURSIVE_PART_P2_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption.
          by rewrite -Constants.q_eq_fieldq_p; assumption.
          by rewrite -Constants.q_eq_fieldq_p; assumption.
          rewrite /mulmod. simplify. rewrite -Constants.R_int /Constants.R W256.of_uintK (pmod_small _ W256.modulus).
          progress. exact modz_ge0.
          apply (int_lt_lt_trans _ Constants.R). rewrite /Constants.R. exact ltz_pmod. rewrite /Constants.R; progress.
          rewrite Constants.OMEGA_int. reflexivity.

          seq 1 3: #pre.
          exists* Primops.reverted{1}. elim*=>reverted.
          case reverted.    
          call{1} pointMulAndAddIntoDest_low_pspec_revert.
          inline*. wp. skip. progress.
          left. progress. left. case H. by progress. by progress.

          wp.
          exists* opening_proof_at_z{2}, pairing_pair_with_generator{2}, z{2}, Primops.memory{1}.
          elim*=> opening_proof_at_z_r pairing_pair_with_generator_r z_r memory_l.
          call (pointMulAndAddIntoDest_low_equiv_mid opening_proof_at_z_r.`1 opening_proof_at_z_r.`2 pairing_pair_with_generator_r.`1 pairing_pair_with_generator_r.`2 z_r PROOF_OPENING_PROOF_AT_Z_X_SLOT PAIRING_PAIR_WITH_GENERATOR_X_SLOT memory_l).
          skip. progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; [
            progress |
            progress;
            apply (int_lt_lt_trans _ FieldR.p); [
              assumption |
              rewrite -Constants.r_eq_fieldr_p /Constants.R; progress
            ]
          ].
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT W256.of_intN'; progress.
          by rewrite /PROOF_OPENING_PROOF_AT_Z_X_SLOT; simplify; rewrite W256.of_intN'; progress.
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT W256.of_intN'; progress.
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT; simplify; rewrite W256.of_intN'; progress.
          by case H; [progress| progress; rewrite H6; progress].
          by case H; [progress| progress; rewrite H7; progress].
          by case H; [progress| progress; rewrite H2; progress].
          by case H; [progress| progress; rewrite H3; progress].
          by case H; [progress| progress; apply uint256_eq_of_eq; rewrite H35; reflexivity].
          case H24. progress. case H25. progress. right.
          progress.
          by case H; progress.
          by case H; [
            progress |
            progress;
            rewrite /STATE_U_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity
          ].
          by case H; [
            progress |
            progress;
            rewrite /STATE_Z_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity
          ].
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_same W256.of_uintK pmod_small; [
              progress; [
                exact FieldQ.ge0_asint |
                apply (int_lt_lt_trans _ FieldQ.p); [
                  exact FieldQ.gtp_asint|
                  rewrite -Constants.q_eq_fieldq_p /Constants.Q; progress
                ]
              ] |
              rewrite /F_to_int_point; progress
            ]
          ].
          by rewrite load_store_same W256.of_uintK pmod_small; [
            progress; [
              exact FieldQ.ge0_asint |
              apply (int_lt_lt_trans _ FieldQ.p); [
                exact FieldQ.gtp_asint|
                rewrite -Constants.q_eq_fieldq_p /Constants.Q; progress
              ]
            ] |
            rewrite /F_to_int_point; progress
          ].
          by case H; [ progress | progress; rewrite /PAIRING_BUFFER_POINT_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PAIRING_BUFFER_POINT_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /VK_RECURSIVE_FLAG_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_RECURSIVE_PART_P1_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_RECURSIVE_PART_P1_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_RECURSIVE_PART_P2_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_RECURSIVE_PART_P2_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          exact F_to_int_point_1_ge_zero.
          exact F_to_int_point_1_lt_p.
          exact F_to_int_point_2_ge_zero.
          exact F_to_int_point_2_lt_p.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          by progress; left; assumption.
          by progress; left; assumption.

          seq 1 3: #pre.
          exists* Primops.reverted{1}. elim*=>reverted.
          case reverted.    
          call{1} pointMulAndAddIntoDest_low_pspec_revert.
          inline*. wp. skip. progress.
          left. progress. left. case H. by progress. by progress.

          wp.
          exists* opening_proof_at_z_omega{2}, pairing_pair_with_generator{2}, zOmega{2}, u{2}, Primops.memory{1}.
          elim*=> opening_proof_at_z_omega_r pairing_pair_with_generator_r zOmega_r u_r memory_l.
          call (pointMulAndAddIntoDest_low_equiv_mid opening_proof_at_z_omega_r.`1 opening_proof_at_z_omega_r.`2 pairing_pair_with_generator_r.`1 pairing_pair_with_generator_r.`2 ((zOmega_r * u_r) %% Constants.R) PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT PAIRING_PAIR_WITH_GENERATOR_X_SLOT memory_l).
          skip. progress.
          case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by rewrite /Constants.R; exact modz_ge0.
          by apply (int_lt_lt_trans _ Constants.R); [
            apply ltz_pmod; rewrite /Constants.R; progress |
            rewrite /Constants.R; progress
          ].
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT W256.of_intN'; progress.
          by rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT; simplify; rewrite W256.of_intN'; progress.
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT W256.of_intN'; progress.
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT; simplify; rewrite W256.of_intN'; progress.
          by case H; [progress| progress; rewrite H8; progress].
          by case H; [progress| progress; rewrite H9; progress].
          by case H; [progress| progress; rewrite H2; progress].
          by case H; [progress| progress; rewrite H3; progress].
          by case H; [
            progress|
            progress; rewrite /mulmod -Constants.R_int; simplify; rewrite H34; reflexivity
          ].
          case H25. progress. case H26. progress. right.
          progress.
          by case H; progress.
          by case H; [
            progress |
            progress;
            rewrite /STATE_U_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity
          ].
          by case H; [
            progress |
            progress;
            rewrite /STATE_Z_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity
          ].
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_same W256.of_uintK pmod_small; [
              progress; [
                exact FieldQ.ge0_asint |
                apply (int_lt_lt_trans _ FieldQ.p); [
                  exact FieldQ.gtp_asint|
                  rewrite -Constants.q_eq_fieldq_p /Constants.Q; progress
                ]
              ] |
              rewrite /F_to_int_point; progress
            ]
          ].
          by rewrite load_store_same W256.of_uintK pmod_small; [
            progress; [
              exact FieldQ.ge0_asint |
              apply (int_lt_lt_trans _ FieldQ.p); [
                exact FieldQ.gtp_asint|
                rewrite -Constants.q_eq_fieldq_p /Constants.Q; progress
              ]
            ] |
            rewrite /F_to_int_point; progress
          ].
          by case H; [ progress | progress; rewrite /PAIRING_BUFFER_POINT_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PAIRING_BUFFER_POINT_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /VK_RECURSIVE_FLAG_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_RECURSIVE_PART_P1_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_RECURSIVE_PART_P1_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_RECURSIVE_PART_P2_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          by case H; [ progress | progress; rewrite /PROOF_RECURSIVE_PART_P2_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
          simplify;
          do 6! ((rewrite load_store_diff; first by progress); first by progress);
          assumption].
          exact F_to_int_point_1_ge_zero.
          exact F_to_int_point_1_lt_p.
          exact F_to_int_point_2_ge_zero.
          exact F_to_int_point_2_lt_p.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          case H. by progress. smt ().
          by progress; left; assumption.
          by progress; left; assumption.

          seq 5 3: (
            (Primops.reverted{1} /\ failed{2}) \/ (
              !Primops.reverted{1} /\ !failed{2} /\
              u{2} = W256.to_uint (load Primops.memory{1} STATE_U_SLOT) /\
              z{2} = W256.to_uint (load Primops.memory{1} STATE_Z_SLOT) /\
              pairing_pair_with_generator{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_GENERATOR_X_SLOT) /\
              pairing_pair_with_generator{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_GENERATOR_Y_SLOT) /\ 
              pairing_buffer_point{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_BUFFER_POINT_X_SLOT) /\
              pairing_buffer_point{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_BUFFER_POINT_Y_SLOT) /\
              pairing_pair_with_x{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_X_X_SLOT) /\
              pairing_pair_with_x{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_X_Y_SLOT) /\
              opening_proof_at_z{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_X_SLOT) /\
              opening_proof_at_z{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_Y_SLOT) /\
              opening_proof_at_z_omega{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT) /\
              opening_proof_at_z_omega{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT) /\
              vk_recursive_flag{2} = bool_of_uint256 (load Primops.memory{1} VK_RECURSIVE_FLAG_SLOT) /\
              recursive_part_p1{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P1_X_SLOT) /\
              recursive_part_p1{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P1_Y_SLOT) /\
              recursive_part_p2{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P2_X_SLOT) /\
              recursive_part_p2{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P2_Y_SLOT) /\
              0 <= pairing_pair_with_generator{2}.`1 < FieldQ.p /\
              0 <= pairing_pair_with_generator{2}.`2 < FieldQ.p /\
              0 <= pairing_buffer_point{2}.`1 < FieldQ.p /\
              0 <= pairing_buffer_point{2}.`2 < FieldQ.p /\
              0 <= pairing_pair_with_x{2}.`1 < FieldQ.p /\
              0 <= pairing_pair_with_x{2}.`2 < FieldQ.p /\
              0 <= opening_proof_at_z{2}.`1 < FieldQ.p /\
              0 <= opening_proof_at_z{2}.`2 < FieldQ.p /\
              0 <= opening_proof_at_z_omega{2}.`1 < FieldQ.p /\
              0 <= opening_proof_at_z_omega{2}.`2 < FieldQ.p /\
              0 <= u{2} < FieldR.p /\
              0 <= z{2} < FieldR.p /\
              u{2} = W256.to_uint u{1} /\
              z{2} = W256.to_uint z{1} /\
              zOmega{2} = W256.to_uint zOmega{1} /\ (
                vk_recursive_flag{2} => (
                  0 <= recursive_part_p1{2}.`1 < FieldQ.p /\
                  0 <= recursive_part_p1{2}.`2 < FieldQ.p /\
                  0 <= recursive_part_p2{2}.`1 < FieldQ.p /\
                  0 <= recursive_part_p2{2}.`2 < FieldQ.p
                )
              )
            )  
          ).
          inline Primops.mload Primops.mstore.
          sp. wp.
          exists* Primops.reverted{1}. elim*=> reverted.
          case reverted. progress.
          call{1} pointMulAndAddIntoDest_low_pspec_revert.
          inline*. wp. skip. progress.
          left. progress. left. by progress.

          progress.
          exists* opening_proof_at_z_omega{2}, opening_proof_at_z{2}, u{2}, Primops.memory{1}.
          elim*=> opening_proof_at_z_omega_r opening_proof_at_z_r u_r memory_l.
          call (pointMulAndAddIntoDest_low_equiv_mid opening_proof_at_z_omega_r.`1 opening_proof_at_z_omega_r.`2 opening_proof_at_z_r.`1 opening_proof_at_z_r.`2 u_r PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT PAIRING_PAIR_WITH_X_X_SLOT memory_l).
          skip. progress.
          exact to_uint_lt_mod.
          by rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT W256.of_intN'; progress.
          by rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT; simplify; rewrite W256.of_intN'; progress.
          by rewrite /PAIRING_PAIR_WITH_X_X_SLOT W256.of_intN'; progress.
          by rewrite /PAIRING_PAIR_WITH_X_X_SLOT; simplify; rewrite W256.of_intN'; progress.
          by rewrite load_store_diff; [
            rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT; progress |
            rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT; progress |
            rewrite load_store_diff; [
              rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT; progress |
              rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT; progress |
              rewrite H7; progress
            ]
          ].
          by rewrite load_store_diff; [
            rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT; progress |
            rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT; progress |
            rewrite load_store_diff; [
              rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT; progress |
              rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT; progress |
              rewrite H8; progress
            ]
          ].
          by rewrite load_store_diff; [
            rewrite /PAIRING_PAIR_WITH_X_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT; progress |
            rewrite /PAIRING_PAIR_WITH_X_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT; progress |
            rewrite load_store_same H5; progress
          ].
          by rewrite load_store_same /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT H6 load_store_diff; progress.
          by apply uint256_eq_of_eq; rewrite H33; reflexivity.
          case H58. progress. case H59. progress. right. progress.
          by rewrite /STATE_U_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite /STATE_Z_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H1 /PAIRING_PAIR_WITH_GENERATOR_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H2 /PAIRING_PAIR_WITH_GENERATOR_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H3 /PAIRING_BUFFER_POINT_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H4 /PAIRING_BUFFER_POINT_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_same /F_to_int_point W256.of_uintK pmod_small; progress; [
              exact FieldQ.ge0_asint |
              apply (int_lt_lt_trans _ FieldQ.p); [exact FieldQ.gtp_asint| rewrite -Constants.q_eq_fieldq_p /Constants.Q; progress]
            ]
          ].
          by rewrite load_store_same /F_to_int_point W256.of_uintK pmod_small; progress; [
            exact FieldQ.ge0_asint |
            apply (int_lt_lt_trans _ FieldQ.p); [exact FieldQ.gtp_asint| rewrite -Constants.q_eq_fieldq_p /Constants.Q; progress]
          ].
          by rewrite H5 /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H6 /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H7 /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H8 /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite /VK_RECURSIVE_FLAG_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H9 /PROOF_RECURSIVE_PART_P1_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H10 /PROOF_RECURSIVE_PART_P1_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H11 /PROOF_RECURSIVE_PART_P2_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          by rewrite H12 /PROOF_RECURSIVE_PART_P2_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_Y_SLOT;
            do 8! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
          exact F_to_int_point_1_ge_zero.
          exact F_to_int_point_1_lt_p.
          exact F_to_int_point_2_ge_zero.
          exact F_to_int_point_2_lt_p.
          by progress; left; progress.
          by progress; left; progress.

          seq 1 3: #pre.
          exists* Primops.reverted{1}. elim*=> reverted.
          case reverted.
          inline*. wp. skip. progress. case H; by progress.
          left. progress. case H; by progress.
          left. progress. case H; by progress.

          exists* Primops.memory{1}, pairing_pair_with_x{2}.
          elim*=> memory_l pairing_pair_with_x_r.
          wp.
          call (pointNegate_low_equiv_mid memory_l PAIRING_PAIR_WITH_X_X_SLOT pairing_pair_with_x_r.`1 pairing_pair_with_x_r.`2).
          skip. progress.
          smt ().
          by rewrite Constants.q_eq_fieldq_p; case H; by progress.
          by rewrite Constants.q_eq_fieldq_p; case H; by progress.
          case H. by progress. progress. rewrite H6. reflexivity.
          case H. by progress. progress. rewrite H7. reflexivity.
          case H. by progress. case H7. by progress. progress. right. progress.
          by rewrite /STATE_U_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              reflexivity
            ]
          ].
          by rewrite /STATE_Z_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              reflexivity
            ]
          ].
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H13; reflexivity
            ]
          ].  
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H14; reflexivity
            ]
          ].
          by rewrite /PAIRING_BUFFER_POINT_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H15; reflexivity
            ]
          ].  
          by rewrite /PAIRING_BUFFER_POINT_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H16; reflexivity
            ]
          ].
          by rewrite /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_same W256.of_uintK pmod_small; progress;
              apply (int_lt_lt_trans _ Constants.Q); [
                assumption |
                rewrite /Constants.Q; progress; reflexivity
              ]
          ].
          by rewrite load_store_same W256.of_uintK pmod_small; progress;
            apply (int_lt_lt_trans _ Constants.Q); [
              assumption |
              rewrite /Constants.Q; progress; reflexivity
            ].
          by rewrite /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H19; reflexivity
            ]
          ].  
          by rewrite /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H20; reflexivity
            ]
          ].
          by rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H21; reflexivity
            ]
          ].  
          by rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H22; reflexivity
            ]
          ].
          by rewrite /VK_RECURSIVE_FLAG_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              reflexivity
            ]
          ].
          by rewrite /PROOF_RECURSIVE_PART_P1_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H23; reflexivity
            ]
          ].  
          by rewrite /PROOF_RECURSIVE_PART_P1_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H24; reflexivity
            ]
          ].
          by rewrite /PROOF_RECURSIVE_PART_P2_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H25; reflexivity
            ]
          ].  
          by rewrite /PROOF_RECURSIVE_PART_P2_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT load_store_diff; [
            progress |
            progress |
            rewrite load_store_diff; [
              progress |
              progress |
              rewrite H26; reflexivity
            ]
          ].
          by rewrite -Constants.q_eq_fieldq_p; assumption.
          by rewrite -Constants.q_eq_fieldq_p; assumption.

          seq 2 1: #pre.
          exists* Primops.reverted{1}. elim*=> reverted.
          case reverted.
          conseq (_: Primops.reverted{1} /\ failed{2} ==> Primops.reverted{1} /\ failed{2}).
          progress. by case H; progress.
          progress. left. by progress.
          inline Primops.mload. sp.
          case (vk_recursive_flag{2}).
          rcondt{2} 1. by progress.
          case (bool_of_uint256 _17{1}).
          rcondt{1} 1. by progress.
          call{1} pointMulAndAddIntoDest_low_pspec_revert.
          call{1} pointMulAndAddIntoDest_low_pspec_revert.
          inline*. wp. skip.
          progress. left. left. assumption.
          rcondf{1} 1. by progress.
          inline*. wp. skip. progress. left. left. assumption.
          rcondf{2} 1. by progress.
          case (bool_of_uint256 _17{1}).
          rcondt{1} 1. by progress.
          call{1} pointMulAndAddIntoDest_low_pspec_revert.
          call{1} pointMulAndAddIntoDest_low_pspec_revert.
          inline*. wp. skip.
          by progress.
          rcondf{1} 1. by progress. skip. by progress.

          case (vk_recursive_flag{2}).
          rcondt{2} 1. by progress.
          rcondt{1} 2. progress. inline*. wp. skip. progress; case H; by progress.
          
          seq 2 1: (
            !Primops.reverted{1} /\ !failed{2} /\
            u{2} = W256.to_uint (load Primops.memory{1} STATE_U_SLOT) /\
            z{2} = W256.to_uint (load Primops.memory{1} STATE_Z_SLOT) /\
            pairing_pair_with_generator{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_GENERATOR_X_SLOT) /\
            pairing_pair_with_generator{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_GENERATOR_Y_SLOT) /\ 
            pairing_buffer_point{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_BUFFER_POINT_X_SLOT) /\
            pairing_buffer_point{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_BUFFER_POINT_Y_SLOT) /\
            pairing_pair_with_x{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_X_X_SLOT) /\
            pairing_pair_with_x{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_X_Y_SLOT) /\
            opening_proof_at_z{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_X_SLOT) /\
            opening_proof_at_z{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_Y_SLOT) /\
            opening_proof_at_z_omega{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT) /\
            opening_proof_at_z_omega{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT) /\
            vk_recursive_flag{2} = bool_of_uint256 (load Primops.memory{1} VK_RECURSIVE_FLAG_SLOT) /\
            recursive_part_p1{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P1_X_SLOT) /\
            recursive_part_p1{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P1_Y_SLOT) /\
            recursive_part_p2{2}.`1 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P2_X_SLOT) /\
            recursive_part_p2{2}.`2 = W256.to_uint (load Primops.memory{1} PROOF_RECURSIVE_PART_P2_Y_SLOT) /\
            0 <= pairing_pair_with_generator{2}.`1 < FieldQ.p /\
            0 <= pairing_pair_with_generator{2}.`2 < FieldQ.p /\
            0 <= pairing_buffer_point{2}.`1 < FieldQ.p /\
            0 <= pairing_buffer_point{2}.`2 < FieldQ.p /\
            0 <= pairing_pair_with_x{2}.`1 < FieldQ.p /\
            0 <= pairing_pair_with_x{2}.`2 < FieldQ.p /\
            0 <= opening_proof_at_z{2}.`1 < FieldQ.p /\
            0 <= opening_proof_at_z{2}.`2 < FieldQ.p /\
            0 <= opening_proof_at_z_omega{2}.`1 < FieldQ.p /\
            0 <= opening_proof_at_z_omega{2}.`2 < FieldQ.p /\
            0 <= u{2} < FieldR.p /\
            0 <= z{2} < FieldR.p /\
            u{2} = W256.to_uint u{1} /\
            z{2} = W256.to_uint z{1} /\
            zOmega{2} = W256.to_uint zOmega{1} /\
            0 <= recursive_part_p1{2}.`1 < FieldQ.p /\
            0 <= recursive_part_p1{2}.`2 < FieldQ.p /\
            0 <= recursive_part_p2{2}.`1 < FieldQ.p /\
            0 <= recursive_part_p2{2}.`2 < FieldQ.p /\
            uu{2} = W256.to_uint uu{1} /\
            vk_recursive_flag{2}
          ).
          inline*. wp. skip. progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; [progress | rewrite H1; progress].
          by case H; [progress | rewrite H1; progress].
          by case H; [progress | rewrite H1; progress].
          by case H; [progress | rewrite H1; progress].
          by case H; [progress | rewrite H1; progress].
          by case H; [progress | rewrite H1; progress].
          by case H; [progress | rewrite H1; progress].
          by case H; [progress | rewrite H1; progress].
          rewrite /mulmod. simplify. rewrite W256.of_uintK (pmod_small _ W256.modulus).
          progress. apply modz_ge0. rewrite -Constants.R_int /Constants.R. by trivial.
          apply (int_lt_lt_trans _ Constants.R). rewrite -Constants.R_int /Constants.R. exact ltz_pmod.
          rewrite /Constants.R. by trivial.
          rewrite -Constants.R_int. case H; progress. rewrite H41. reflexivity.

          seq 1 3: (
            #pre \/ (Primops.reverted{1} /\ failed{2})
          ).
          wp.
          exists* recursive_part_p1{2}, pairing_pair_with_generator{2}, uu{2}, Primops.memory{1}.
          elim*=> recursive_part_p1_r pairing_pair_with_generator_r uu_r memory_l.
          call (pointMulAndAddIntoDest_low_equiv_mid recursive_part_p1_r.`1 recursive_part_p1_r.`2 pairing_pair_with_generator_r.`1 pairing_pair_with_generator_r.`2 uu_r PROOF_RECURSIVE_PART_P1_X_SLOT PAIRING_PAIR_WITH_GENERATOR_X_SLOT memory_l).
          skip. progress.
          exact to_uint_ge_zero. exact to_uint_lt_mod.
          by rewrite /PROOF_RECURSIVE_PART_P1_X_SLOT W256.of_intN'; progress.
          by rewrite /PROOF_RECURSIVE_PART_P1_X_SLOT; simplify; rewrite W256.of_intN'; progress.
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT W256.of_intN'; progress.
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT; simplify; rewrite W256.of_intN'; progress.
          by rewrite H11; progress.
          by rewrite H12; progress.
          by rewrite H1; progress.
          by rewrite H2; progress.
          case H73. progress. case H74. progress.
            left. progress.
            by rewrite /STATE_U_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
            by rewrite /STATE_Z_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
            rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT load_store_diff.
              by progress.
              by progress.
              rewrite load_store_same /F_to_int_point. simplify.
              rewrite W256.of_uintK pmod_small. progress.
                exact FieldQ.ge0_asint.
                apply (int_lt_lt_trans _ FieldQ.p).
                  exact FieldQ.gtp_asint. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial.
                reflexivity.
            rewrite load_store_same /F_to_int_point. simplify.
            rewrite W256.of_uintK pmod_small. progress.
            exact FieldQ.ge0_asint.
            apply (int_lt_lt_trans _ FieldQ.p).
            exact FieldQ.gtp_asint. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial.
            reflexivity.
            by rewrite /PAIRING_BUFFER_POINT_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H3; reflexivity.
            by rewrite /PAIRING_BUFFER_POINT_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H4; reflexivity.
            by rewrite /PAIRING_PAIR_WITH_X_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H5; reflexivity.
            by rewrite /PAIRING_PAIR_WITH_X_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H6; reflexivity.
            by rewrite /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H7; reflexivity.
            by rewrite /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H8; reflexivity.
            by rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H9; reflexivity.
            by rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H10; reflexivity.
            by rewrite /VK_RECURSIVE_FLAG_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            reflexivity.
            by rewrite /PROOF_RECURSIVE_PART_P1_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H11; reflexivity.
            by rewrite /PROOF_RECURSIVE_PART_P1_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H12; reflexivity.
            by rewrite /PROOF_RECURSIVE_PART_P2_X_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H13; reflexivity.
            by rewrite /PROOF_RECURSIVE_PART_P2_Y_SLOT /PAIRING_PAIR_WITH_GENERATOR_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            rewrite H14; reflexivity.
            exact F_to_int_point_1_ge_zero.
            exact F_to_int_point_1_lt_p.
            exact F_to_int_point_2_ge_zero.
            exact F_to_int_point_2_lt_p.
            by progress.
            by progress.

          case (Primops.reverted{1}).
          call{1} pointMulAndAddIntoDest_low_pspec_revert.
          inline*. wp. skip. progress. left. progress. left. case H. by progress. by progress.

          wp.
          exists* recursive_part_p2{2}, pairing_pair_with_x{2}, uu{2}, Primops.memory{1}.
          elim*=> recursive_part_p2_r pairing_pair_with_x_r uu_r memory_l.
          call (pointMulAndAddIntoDest_low_equiv_mid recursive_part_p2_r.`1 recursive_part_p2_r.`2 pairing_pair_with_x_r.`1 pairing_pair_with_x_r.`2 uu_r PROOF_RECURSIVE_PART_P2_X_SLOT PAIRING_PAIR_WITH_X_X_SLOT memory_l).
          skip. progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          case H. by progress; exact to_uint_ge_zero. by progress.
          case H. by progress; exact to_uint_lt_mod. by progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by rewrite /PROOF_RECURSIVE_PART_P2_X_SLOT W256.of_intN'; progress.
          by rewrite /PROOF_RECURSIVE_PART_P2_X_SLOT; simplify; rewrite W256.of_intN'; progress.
          by rewrite /PAIRING_PAIR_WITH_X_X_SLOT W256.of_intN'; progress.
          by rewrite /PAIRING_PAIR_WITH_X_X_SLOT; simplify; rewrite W256.of_intN'; progress.
          case H. progress. rewrite H14. by progress. by progress.
          case H. progress. rewrite H15. by progress. by progress.
          case H. progress. rewrite H6. by progress. by progress.
          case H. progress. rewrite H7. by progress. by progress.
          case H. by progress. by progress.
          case H24. progress. case H25. progress. right. progress.
          by case H; progress.
          by rewrite /STATE_U_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /STATE_Z_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /PAIRING_PAIR_WITH_GENERATOR_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /PAIRING_BUFFER_POINT_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /PAIRING_BUFFER_POINT_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          rewrite load_store_diff.
            by rewrite /PAIRING_PAIR_WITH_X_X_SLOT; progress.
            by rewrite /PAIRING_PAIR_WITH_X_X_SLOT; progress.
          rewrite load_store_same /F_to_int_point W256.of_uintK pmod_small.
            progress. exact FieldQ.ge0_asint.
            apply (int_lt_lt_trans _ FieldQ.p). exact FieldQ.gtp_asint. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial. by progress.
          rewrite load_store_same /F_to_int_point W256.of_uintK pmod_small.
            progress. exact FieldQ.ge0_asint.
            apply (int_lt_lt_trans _ FieldQ.p). exact FieldQ.gtp_asint. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial. by progress.
          by rewrite /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /PROOF_OPENING_PROOF_AT_Z_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /VK_RECURSIVE_FLAG_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /PROOF_RECURSIVE_PART_P1_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /PROOF_RECURSIVE_PART_P1_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /PROOF_RECURSIVE_PART_P2_X_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by rewrite /VK_RECURSIVE_FLAG_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
          by rewrite /PROOF_RECURSIVE_PART_P2_Y_SLOT /PAIRING_PAIR_WITH_X_X_SLOT;
            do 6! ((rewrite load_store_diff; first by progress); first by progress);
            case H; progress; case H; by progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          exact F_to_int_point_1_ge_zero.
          exact F_to_int_point_1_lt_p.
          exact F_to_int_point_2_ge_zero.
          exact F_to_int_point_2_lt_p.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by case H; progress.
          by progress. by progress.

          rcondf{2} 1. by progress.
          inline Primops.mload. sp. rcondf{1} 1. progress. skip. progress. case H. by progress. by progress.
          skip. by progress.

          case (Primops.reverted{1}).
          conseq (_ : (Primops.reverted{1} /\ failed{2}) ==> (Primops.reverted{1} /\ failed{2})).
          progress. by case H; progress.
          progress. case H. progress. rewrite H1 H2. reflexivity.
          by progress.
          seq 18 0: #pre.
          call{1} ConcretePrimops.staticcall_pspec_revert.
          inline*. wp. skip. by progress.
          case (bool_of_uint256 (PurePrimops.iszero success{1})).
          rcondt{1} 1. by progress.
          seq 1 0: #pre. call{1} revertWithMessage_low_pspec. skip. by progress.
          inline Primops.mload. sp.
          case (bool_of_uint256 (PurePrimops.iszero _50{1})).
          rcondt{1} 1. by progress.
          call{1} revertWithMessage_low_pspec. skip. progress. left. assumption.
          rcondf{1} 1. by progress.
          skip. progress. left. assumption.
          rcondf{1} 1. by progress.
          inline Primops.mload. sp.
          case (bool_of_uint256 (PurePrimops.iszero _50{1})).
          rcondt{1} 1. by progress.
          call{1} revertWithMessage_low_pspec. skip. progress. left. assumption.
          rcondf{1} 1. by progress.
          skip. progress. left. assumption.

          conseq (_ : (
            !Primops.reverted{1} /\
            !failed{2} /\
            pairing_pair_with_generator{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_GENERATOR_X_SLOT) /\
            pairing_pair_with_generator{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_GENERATOR_Y_SLOT) /\
            pairing_pair_with_x{2}.`1 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_X_X_SLOT) /\
            pairing_pair_with_x{2}.`2 = W256.to_uint (load Primops.memory{1} PAIRING_PAIR_WITH_X_Y_SLOT) /\
            0 <= pairing_pair_with_generator{2}.`1 < FieldQ.p /\
            0 <= pairing_pair_with_generator{2}.`2 < FieldQ.p /\
            0 <= pairing_pair_with_x{2}.`1 < FieldQ.p /\
            0 <= pairing_pair_with_x{2}.`2 < FieldQ.p
          ) ==> (
            Primops.reverted{1} = failed{2}
          )).
          by progress; case H; progress.

          seq 18 2: (
            !Primops.reverted{1} /\
            failed{2} = (
              success{1} = W256.zero \/
              load Primops.memory{1} W256.zero = W256.zero
            )
          ).
          inline Primops.mstore Primops.mload Primops.gas. sp.
          exists* Primops.memory{1}, pairing_pair_with_generator{2}, pairing_pair_with_x{2}.
          elim*=> memory_l pairing_pair_with_generator_r pairing_pair_with_x_r.
          progress.
          call{1} (
            ConcretePrimops.staticcall_ec_pairing_pspec
              memory_l
              (W256.of_int pairing_pair_with_generator_r.`1, W256.of_int pairing_pair_with_generator_r.`2)
              (W256.of_int pairing_pair_with_x_r.`1, W256.of_int pairing_pair_with_x_r.`2)
              ((G2_ELEMENTS_0_X1, G2_ELEMENTS_0_X2), (G2_ELEMENTS_0_Y1, G2_ELEMENTS_0_Y2))
              ((G2_ELEMENTS_1_X1, G2_ELEMENTS_1_X2), (G2_ELEMENTS_1_Y1, G2_ELEMENTS_1_Y2))
              W256.zero
              W256.zero
          ).
          skip. progress.
          do 11! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite load_store_same H1. by progress.
          do 10! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite load_store_same H2.
          rewrite load_store_diff.
            by rewrite /PAIRING_PAIR_WITH_GENERATOR_Y_SLOT; progress.
            by rewrite /PAIRING_PAIR_WITH_GENERATOR_Y_SLOT; progress.
            by progress.
          do 9! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite load_store_same. reflexivity.
          do 8! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite load_store_same. reflexivity.
          do 7! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite load_store_same. reflexivity.
          do 6! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite load_store_same. reflexivity.
          do 5! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite load_store_same.
          rewrite /PAIRING_PAIR_WITH_X_X_SLOT.
          do 6! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite H3. by progress.
          do 4! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite load_store_same.
          rewrite /PAIRING_PAIR_WITH_X_Y_SLOT.
          do 7! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite H4. by progress.
          do 3! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite load_store_same. reflexivity.
          do 2! ((rewrite load_store_diff; first by progress); first by progress).
          rewrite load_store_same. reflexivity.
          (rewrite load_store_diff; first by progress); first by progress.
          rewrite load_store_same. reflexivity.
          rewrite load_store_same. reflexivity.
          case (ConcretePrimops.staticcall_ec_pairing_should_succeed
            ((W256.of_int pairing_pair_with_generator{2}.`1),
             (W256.of_int pairing_pair_with_generator{2}.`2))
            ((W256.of_int pairing_pair_with_x{2}.`1),
             (W256.of_int pairing_pair_with_x{2}.`2))
            ((G2_ELEMENTS_0_X1, G2_ELEMENTS_0_X2),
             (G2_ELEMENTS_0_Y1, G2_ELEMENTS_0_Y2))
            ((G2_ELEMENTS_1_X1, G2_ELEMENTS_1_X2),
             (G2_ELEMENTS_1_Y1, G2_ELEMENTS_1_Y2))).
          progress.
          have H_res: result = W256.one by smt ().
          rewrite H0. rewrite H_res.
          have ->: W256.one <> W256.zero by smt(@W256).
          progress.
          have ->: (load memory_L0 W256.zero) = ((ConcretePrimops.ecPairing_precompile_unsafe_cast
            ((W256.of_int pairing_pair_with_generator{2}.`1),
             (W256.of_int pairing_pair_with_generator{2}.`2))
            ((W256.of_int pairing_pair_with_x{2}.`1),
             (W256.of_int pairing_pair_with_x{2}.`2))
            ((G2_ELEMENTS_0_X1, G2_ELEMENTS_0_X2),
             (G2_ELEMENTS_0_Y1, G2_ELEMENTS_0_Y2))
            ((G2_ELEMENTS_1_X1, G2_ELEMENTS_1_X2),
             (G2_ELEMENTS_1_Y1, G2_ELEMENTS_1_Y2)))) by smt(load_store_same).
          rewrite /ecPairing_precompile_unsafe_cast. simplify.
          have ->: forall (b: bool), (uint256_of_bool b = W256.zero) = !b.
            rewrite /uint256_of_bool. progress. case b. progress. smt (@W256). by progress.
          congr. congr. congr. congr. congr.
          rewrite W256.of_uintK pmod_small. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial. reflexivity.
          rewrite W256.of_uintK pmod_small. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial. reflexivity.
          rewrite Constants.G2_element_0_int. by progress.
          congr.          
          rewrite W256.of_uintK pmod_small. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial.
          rewrite W256.of_uintK pmod_small. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial. reflexivity.          
          rewrite Constants.G2_element_1_int. by progress.


          progress.
          have H_res: result = W256.zero by smt ().
          rewrite H0. rewrite H_res.
          progress.
          pose pairing := ecPairing_precompile _ _.
          have ->: pairing = None.
            apply eq_none_of_is_none.
            rewrite /pairing.
            have H_none: is_none
              (ecPairing_precompile
                ((FieldQ.inF (W256.to_uint (W256.of_int pairing_pair_with_generator{2}.`1)),
                 FieldQ.inF (W256.to_uint (W256.of_int pairing_pair_with_generator{2}.`2))),
                ((FieldQ.inF (W256.to_uint (W256.of_int Constants.G2_ELEMENT_0.`1.`1)),
                 FieldQ.inF (W256.to_uint (W256.of_int Constants.G2_ELEMENT_0.`1.`2))),
                (FieldQ.inF (W256.to_uint (W256.of_int Constants.G2_ELEMENT_0.`2.`1)),
                FieldQ.inF (W256.to_uint (W256.of_int Constants.G2_ELEMENT_0.`2.`2)))))
                ((FieldQ.inF (W256.to_uint (W256.of_int pairing_pair_with_x{2}.`1)),
                FieldQ.inF (W256.to_uint (W256.of_int pairing_pair_with_x{2}.`2))),
                ((FieldQ.inF (W256.to_uint (W256.of_int Constants.G2_ELEMENT_1.`1.`1)),
                FieldQ.inF (W256.to_uint (W256.of_int Constants.G2_ELEMENT_1.`1.`2))),
                (FieldQ.inF (W256.to_uint (W256.of_int Constants.G2_ELEMENT_1.`2.`1)),
                FieldQ.inF (W256.to_uint (W256.of_int Constants.G2_ELEMENT_1.`2.`2)))))).
                apply (
                  ConcretePrimops.ecPairing_precomp_is_none_of_should_not_succeed
                    (W256.of_int pairing_pair_with_generator{2}.`1, W256.of_int pairing_pair_with_generator{2}.`2)
                    (W256.of_int pairing_pair_with_x{2}.`1, W256.of_int pairing_pair_with_x{2}.`2)
                    
                      (
                        (W256.of_int Constants.G2_ELEMENT_0.`1.`1, W256.of_int Constants.G2_ELEMENT_0.`1.`2),
                        (W256.of_int Constants.G2_ELEMENT_0.`2.`1, W256.of_int Constants.G2_ELEMENT_0.`2.`2)
                      )
                      (
                        (W256.of_int Constants.G2_ELEMENT_1.`1.`1, W256.of_int Constants.G2_ELEMENT_1.`1.`2),
                        (W256.of_int Constants.G2_ELEMENT_1.`2.`1, W256.of_int Constants.G2_ELEMENT_1.`2.`2)
                      )
                    
                ). progress.
                rewrite W256.of_uintK pmod_small. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial. assumption.
                rewrite W256.of_uintK pmod_small. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial. assumption.
                rewrite W256.of_uintK pmod_small. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial. assumption.
                rewrite W256.of_uintK pmod_small. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial. assumption.
                rewrite -Constants.q_eq_fieldq_p /Constants.Q /Constants.G2_ELEMENT_0. by progress.
                rewrite -Constants.q_eq_fieldq_p /Constants.Q /Constants.G2_ELEMENT_0. by progress.
                rewrite -Constants.q_eq_fieldq_p /Constants.Q /Constants.G2_ELEMENT_0. by progress.
                rewrite -Constants.q_eq_fieldq_p /Constants.Q /Constants.G2_ELEMENT_0. by progress.
                rewrite -Constants.q_eq_fieldq_p /Constants.Q /Constants.G2_ELEMENT_1. by progress.
                rewrite -Constants.q_eq_fieldq_p /Constants.Q /Constants.G2_ELEMENT_1. by progress.
                rewrite -Constants.q_eq_fieldq_p /Constants.Q /Constants.G2_ELEMENT_1. by progress.
                rewrite -Constants.q_eq_fieldq_p /Constants.Q /Constants.G2_ELEMENT_1. by progress.
                rewrite Constants.G2_element_0_int.
                rewrite Constants.G2_element_1_int. by progress.
            do rewrite W256.of_uintK in H_none.
            rewrite pmod_small in H_none. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial.
            rewrite pmod_small in H_none. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial.
            rewrite pmod_small in H_none. rewrite /Constants.G2_ELEMENT_0. by progress.
            rewrite pmod_small in H_none. rewrite /Constants.G2_ELEMENT_0. by progress.
            rewrite pmod_small in H_none. rewrite /Constants.G2_ELEMENT_0. by progress.
            rewrite pmod_small in H_none. rewrite /Constants.G2_ELEMENT_0. by progress.
            rewrite pmod_small in H_none. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial.
            rewrite pmod_small in H_none. progress. apply (int_lt_lt_trans _ FieldQ.p). assumption. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by trivial.
            rewrite pmod_small in H_none. rewrite /Constants.G2_ELEMENT_1. by progress.
            rewrite pmod_small in H_none. rewrite /Constants.G2_ELEMENT_1. by progress.
            rewrite pmod_small in H_none. rewrite /Constants.G2_ELEMENT_1. by progress.
            rewrite pmod_small in H_none. rewrite /Constants.G2_ELEMENT_1. by progress.
          assumption.
          by progress.
          
          case (success{1} = W256.zero).
          rcondt{1} 1. progress. skip. progress. rewrite /bool_of_uint256 /iszero. progress. smt (@W256).
          seq 1 0: (Primops.reverted{1} /\ failed{2}).
          call{1} revertWithMessage_low_pspec. skip. by progress.
          inline Primops.mload. sp.
          case (bool_of_uint256 (PurePrimops.iszero _50{1})).
          rcondt{1} 1. progress.
          call{1} revertWithMessage_low_pspec. skip. progress. rewrite H0 H2. reflexivity.
          rcondf{1} 1. by progress. skip. progress. rewrite H H0. reflexivity.
          
          rcondf{1} 1. progress. skip. progress. rewrite /iszero /bool_of_uint256 H0. by progress.
          inline Primops.mload. sp.
          case (bool_of_uint256 (PurePrimops.iszero _50{1})).
          rcondt{1} 1. progress.
          call{1} revertWithMessage_low_pspec. skip. progress. rewrite H0 H2. progress. rewrite /bool_of_uint256 /iszero in H1. smt ().
          rcondf{1} 1. progress. skip. progress. rewrite H H0. progress. rewrite /bool_of_uint256 /iszero in H1. smt (@W256).
qed.

lemma finalPairing_mid_equiv_high_encapsulated:
    equiv [
      FinalPairing.mid ~ FinalPairing.high_encapsulated:
      u{1} = FieldR.asint u{2} /\
      z{1} = FieldR.asint z{2} /\
      pairing_pair_with_generator{1} = F_to_int_point (aspoint_G1 pairing_pair_with_generator{2}) /\
      pairing_buffer_point{1} = F_to_int_point (aspoint_G1 pairing_buffer_point{2}) /\
      opening_proof_at_z{1} = F_to_int_point (aspoint_G1 opening_proof_at_z{2}) /\
      opening_proof_at_z_omega{1} = F_to_int_point (aspoint_G1 opening_proof_at_z_omega{2}) /\
      ={vk_recursive_flag} /\
      recursive_part_p1{1} = F_to_int_point (aspoint_G1 recursive_part_p1{2}) /\
      recursive_part_p2{1} = F_to_int_point (aspoint_G1 recursive_part_p2{2}) ==>
      ={res}
    ].
    proof.
      proc.
      simplify.
      seq 6 1: (
        #pre /\
        !failed{1} /\
        zOmega{1} = FieldR.asint (z{2} * Constants.OMEGAFr)        
      ).
      wp. sp.
      call pointSubAssign_mid_equiv_high. skip. progress.
      rewrite FieldR.mulE Constants.omega_eq_omegaFr Constants.r_eq_fieldr_p. reflexivity.

      seq 3 1: #pre.
      wp. call pointMulAndAddIntoDest_mid_equiv_high. skip. by progress.

      seq 3 1: #pre.
      wp. call pointMulAndAddIntoDest_mid_equiv_high. skip. progress.
      do rewrite FieldR.mulE.
      rewrite Constants.r_eq_fieldr_p. reflexivity.

      seq 3 1: (
        #pre /\
        pairing_pair_with_x{1} = F_to_int_point(aspoint_G1 pairing_pair_with_x{2})
      ).
      wp. call pointMulAndAddIntoDest_mid_equiv_high. skip. by progress.

      seq 3 1: #pre.
      wp. call pointNegate_mid_equiv_high. skip. by progress.

      if. progress.

      seq 4 1: (
        #pre /\
        uu{1} = FieldR.asint (u{2} * u{2})
      ).
      sp. wp. call pointMulAndAddIntoDest_mid_equiv_high. skip. progress.
      rewrite FieldR.mulE Constants.r_eq_fieldr_p. reflexivity.

      seq 3 1: #pre.
      wp. call pointMulAndAddIntoDest_mid_equiv_high. skip. by progress.

      wp. skip. progress.
      rewrite H. progress.
      rewrite F_to_int_point_inzmod_1.
      rewrite F_to_int_point_inzmod_2.
      rewrite F_to_int_point_inzmod_1.
      rewrite F_to_int_point_inzmod_2.
      rewrite Constants.G2_ELEMENT_0_G_aspoint_1_1.
      rewrite Constants.G2_ELEMENT_0_G_aspoint_1_2.
      rewrite Constants.G2_ELEMENT_0_G_aspoint_2_1.
      rewrite Constants.G2_ELEMENT_0_G_aspoint_2_2.
      rewrite Constants.G2_ELEMENT_1_G_aspoint_1_1.
      rewrite Constants.G2_ELEMENT_1_G_aspoint_1_2.
      rewrite Constants.G2_ELEMENT_1_G_aspoint_2_1.
      rewrite Constants.G2_ELEMENT_1_G_aspoint_2_2.
      do rewrite FieldQ.asintK.
      pose pairing := ecPairing_precompile _ _.
      have H_pairing: pairing = ecPairing_precompile (aspoint_G1 pairing_pair_with_generator{2}, aspoint_G2 Constants.G2_ELEMENT_0_G) (aspoint_G1 pairing_pair_with_x{2}, aspoint_G2 Constants.G2_ELEMENT_1_G) by smt ().
      have H_pairing_some: pairing = Some (e (pairing_pair_with_generator{2} + pairing_pair_with_x{2}) (Constants.G2_ELEMENT_0_G + Constants.G2_ELEMENT_1_G) = G.e) by smt (ecPairing_def).
      rewrite H_pairing_some.
      by progress.

      wp. skip. progress.
      rewrite H. progress.
      rewrite F_to_int_point_inzmod_1.
      rewrite F_to_int_point_inzmod_2.
      rewrite F_to_int_point_inzmod_1.
      rewrite F_to_int_point_inzmod_2.
      rewrite Constants.G2_ELEMENT_0_G_aspoint_1_1.
      rewrite Constants.G2_ELEMENT_0_G_aspoint_1_2.
      rewrite Constants.G2_ELEMENT_0_G_aspoint_2_1.
      rewrite Constants.G2_ELEMENT_0_G_aspoint_2_2.
      rewrite Constants.G2_ELEMENT_1_G_aspoint_1_1.
      rewrite Constants.G2_ELEMENT_1_G_aspoint_1_2.
      rewrite Constants.G2_ELEMENT_1_G_aspoint_2_1.
      rewrite Constants.G2_ELEMENT_1_G_aspoint_2_2.
      do rewrite FieldQ.asintK.
      pose pairing := ecPairing_precompile _ _.
      have H_pairing: pairing = ecPairing_precompile (aspoint_G1 pairing_pair_with_generator{2}, aspoint_G2 Constants.G2_ELEMENT_0_G) (aspoint_G1 pairing_pair_with_x{2}, aspoint_G2 Constants.G2_ELEMENT_1_G) by smt ().
      have H_pairing_some: pairing = Some (e (pairing_pair_with_generator{2} + pairing_pair_with_x{2}) (Constants.G2_ELEMENT_0_G + Constants.G2_ELEMENT_1_G) = G.e) by smt (ecPairing_def).
      rewrite H_pairing_some.
      by progress.
qed.

lemma finalPairing_mid_equiv_high:
    equiv [
      FinalPairing.mid ~ FinalPairing.high:
      u{1} = FieldR.asint u{2} /\
      z{1} = FieldR.asint z{2} /\
      pairing_pair_with_generator{1} = F_to_int_point (aspoint_G1 pairing_pair_with_generator{2}) /\
      pairing_buffer_point{1} = F_to_int_point (aspoint_G1 pairing_buffer_point{2}) /\
      opening_proof_at_z{1} = F_to_int_point (aspoint_G1 opening_proof_at_z{2}) /\
      opening_proof_at_z_omega{1} = F_to_int_point (aspoint_G1 opening_proof_at_z_omega{2}) /\
      ={vk_recursive_flag} /\
      recursive_part_p1{1} = F_to_int_point (aspoint_G1 recursive_part_p1{2}) /\
      recursive_part_p2{1} = F_to_int_point (aspoint_G1 recursive_part_p2{2}) ==>
      ={res}
    ].
    proof.
      transitivity FinalPairing.high_encapsulated
      (
        u{1} = FieldR.asint u{2} /\
        z{1} = FieldR.asint z{2} /\
        pairing_pair_with_generator{1} = F_to_int_point (aspoint_G1 pairing_pair_with_generator{2}) /\
        pairing_buffer_point{1} = F_to_int_point (aspoint_G1 pairing_buffer_point{2}) /\
        opening_proof_at_z{1} = F_to_int_point (aspoint_G1 opening_proof_at_z{2}) /\
        opening_proof_at_z_omega{1} = F_to_int_point (aspoint_G1 opening_proof_at_z_omega{2}) /\
        ={vk_recursive_flag} /\
        recursive_part_p1{1} = F_to_int_point (aspoint_G1 recursive_part_p1{2}) /\
        recursive_part_p2{1} = F_to_int_point (aspoint_G1 recursive_part_p2{2}) ==>
        ={res}
      )
      (
        ={arg} ==> ={res}
      ).
      progress. exists arg{2}. by progress.
      by progress.
      exact finalPairing_mid_equiv_high_encapsulated.
      proc.
      inline*. wp. skip. by progress.
qed.
