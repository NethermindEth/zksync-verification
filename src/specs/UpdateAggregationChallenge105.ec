require        Constants.
require import Field.
require import PointMulAndAddIntoDest.
require import PurePrimops.
require import UInt256.
require import Utils.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

module UpdateAggregationChallenge_105 = {
  proc low(queriesCommitmentPoint : uint256, valueAtZ_Omega : uint256, previousCoeff : uint256, curAggregationChallenge : uint256, curAggregatedOpeningAtZ_Omega : uint256): (uint256 * uint256) = {
    var newAggregationChallenge, newAggregatedOpeningAtZ_Omega, _3, _5, _6, finalCoeff, tmp375, _8, _9;
    _3 <@ Primops.mload(STATE_V_SLOT);
    newAggregationChallenge <- (PurePrimops.mulmod curAggregationChallenge _3 R_MOD);
    _5 <@ Primops.mload(STATE_U_SLOT);
    _6 <- (PurePrimops.mulmod newAggregationChallenge _5 R_MOD);
    finalCoeff <- (PurePrimops.addmod previousCoeff _6 R_MOD);
    tmp375 <@ PointMulAndAddIntoDest.low(queriesCommitmentPoint, finalCoeff, AGGREGATED_AT_Z_OMEGA_X_SLOT);
    _8 <@ Primops.mload(valueAtZ_Omega);
    _9 <- (PurePrimops.mulmod newAggregationChallenge _8 R_MOD);
    newAggregatedOpeningAtZ_Omega <- (PurePrimops.addmod curAggregatedOpeningAtZ_Omega _9 R_MOD);
    return (newAggregationChallenge, newAggregatedOpeningAtZ_Omega);
  }

  proc mid(queriesCommitmentPoint : int * int, valueAtZ_Omega : int, previousCoeff : int, currAggregationChallenge : int, curAggregatedOpeningAtZ_Omega : int, v_challenge : int, u_challenge : int, currAggregatedAtZOmegaXSlot : int * int) : (int * int * (int * int)) option = {
      var newAggregationChallenge, finalCoeff, newAggregatedOpeningAtZ_Omega, mNewAggregateAtZOmegaXSlot, newAggregateAtZOmegaXSlot, ret; 
      newAggregationChallenge <- (v_challenge * currAggregationChallenge) %% Constants.R;
      finalCoeff <- (u_challenge * v_challenge * currAggregationChallenge + previousCoeff) %% Constants.R;
      mNewAggregateAtZOmegaXSlot <@ PointMulAndAddIntoDest.mid(queriesCommitmentPoint.`1, queriesCommitmentPoint.`2, finalCoeff, currAggregatedAtZOmegaXSlot.`1, currAggregatedAtZOmegaXSlot.`2);
      if (is_some mNewAggregateAtZOmegaXSlot) {
        newAggregateAtZOmegaXSlot <- odflt (0, 0) mNewAggregateAtZOmegaXSlot;
        newAggregatedOpeningAtZ_Omega <- (newAggregationChallenge * valueAtZ_Omega + curAggregatedOpeningAtZ_Omega) %% Constants.R;
        ret   <- Some (newAggregationChallenge, newAggregatedOpeningAtZ_Omega, newAggregateAtZOmegaXSlot);
      } else {
          ret <- None;
      }
      return ret;
    }
    
}.

lemma updateAggregationChallenge_105_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_updateAggregationChallenge_105 ~ UpdateAggregationChallenge_105.low :
      ={arg, glob UpdateAggregationChallenge_105} ==>
      ={res, glob UpdateAggregationChallenge_105}
    ].
proof.
  proc.
  inline Primops.mload. wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  skip. rewrite /Constants.R. by progress.
qed.

op UpdateAggregationChallenge105_footprint (x y x' y' : int) (currAggregatedAtZXSlot : int * int) (mem_0 : mem) =
  let mem_1 = store mem_0 W256.zero (W256.of_int x) in
  let mem_2 = store mem_1 (W256.of_int 32) (W256.of_int y) in
  let mem_3 = store mem_2 (W256.of_int 64) (W256.of_int currAggregatedAtZXSlot.`1) in
  let mem_4 = store mem_3 (W256.of_int 96) (W256.of_int currAggregatedAtZXSlot.`2) in
  let mem_5 = store mem_4 AGGREGATED_AT_Z_OMEGA_X_SLOT (W256.of_int x') in
  store mem_5 (AGGREGATED_AT_Z_OMEGA_X_SLOT + W256.of_int 32) (W256.of_int y').

lemma updateAggregationChallenge_105_low_equiv_mid (queriesCommitmentPoint : int * int) (valueAtZ_Omega : int) (previousCoeff : int) (currAggregationChallenge : int) (curAggregatedOpeningAtZ_Omega : int) (v_challenge : int) (u_challenge : int) (currAggregatedAtZOmegaXSlot : int * int) (queriesCommitmentPoint_addr valueAtZOmega_addr : uint256) (memory0 : MemoryMap.mem) : equiv [
    UpdateAggregationChallenge_105.low ~ UpdateAggregationChallenge_105.mid :
    Primops.memory{1} = memory0 /\
    0 <= queriesCommitmentPoint.`1 < Constants.Q /\
    0 <= queriesCommitmentPoint.`2 < Constants.Q /\
    0 <= currAggregatedAtZOmegaXSlot.`1 < Constants.Q /\
    0 <= currAggregatedAtZOmegaXSlot.`2 < Constants.Q /\
    0 <= valueAtZ_Omega < Constants.R /\
    0 <= previousCoeff < Constants.R /\
    0 <= currAggregationChallenge < Constants.R /\
    0 <= curAggregatedOpeningAtZ_Omega < Constants.R /\
    0 <= v_challenge < Constants.R /\
    0 <= u_challenge < Constants.R /\
    W256.of_int 128 <= queriesCommitmentPoint_addr /\
    W256.of_int 64 <= - queriesCommitmentPoint_addr /\
    W256.of_int 128 <= queriesCommitmentPoint_addr + W256.of_int 32 /\
    W256.of_int 32 <= - (queriesCommitmentPoint_addr + W256.of_int 32) /\
    W256.of_int 128 <= valueAtZOmega_addr /\
    W256.of_int 32 <= -valueAtZOmega_addr /\
    W256.of_int 32 <= valueAtZOmega_addr - (AGGREGATED_AT_Z_OMEGA_X_SLOT + W256.of_int 32) /\
    W256.of_int 32 <= AGGREGATED_AT_Z_OMEGA_X_SLOT - valueAtZOmega_addr /\
    W256.of_int 32 <= valueAtZOmega_addr - AGGREGATED_AT_Z_OMEGA_X_SLOT /\
    W256.of_int 32 <= (AGGREGATED_AT_Z_OMEGA_X_SLOT + W256.of_int 32) - valueAtZOmega_addr /\
    arg{1} = (queriesCommitmentPoint_addr, valueAtZOmega_addr, W256.of_int previousCoeff, W256.of_int currAggregationChallenge, W256.of_int curAggregatedOpeningAtZ_Omega) /\
    arg{2} = (queriesCommitmentPoint, valueAtZ_Omega, previousCoeff, currAggregationChallenge, curAggregatedOpeningAtZ_Omega, v_challenge, u_challenge, currAggregatedAtZOmegaXSlot) /\
    PurePrimops.mload memory0 STATE_V_SLOT = W256.of_int v_challenge /\
    PurePrimops.mload memory0 STATE_U_SLOT = W256.of_int u_challenge /\
    PurePrimops.mload memory0 valueAtZOmega_addr = W256.of_int valueAtZ_Omega /\
    PurePrimops.mload memory0 queriesCommitmentPoint_addr = W256.of_int queriesCommitmentPoint.`1 /\
    PurePrimops.mload memory0 (queriesCommitmentPoint_addr + W256.of_int 32) = W256.of_int queriesCommitmentPoint.`2 /\
    PurePrimops.mload memory0  AGGREGATED_AT_Z_OMEGA_X_SLOT = W256.of_int currAggregatedAtZOmegaXSlot.`1 /\
    PurePrimops.mload memory0 (AGGREGATED_AT_Z_OMEGA_X_SLOT + W256.of_int 32) = W256.of_int currAggregatedAtZOmegaXSlot.`2 /\
      !Primops.reverted{1}
      ==>
      (res{2} = None /\ Primops.reverted{1}) \/
      (
        exists (newAggregationChallenge newAggregatedOpeningAtZ : int) (newAggregateAtZXSlot : int * int),
        res{2} = Some (newAggregationChallenge, newAggregatedOpeningAtZ, newAggregateAtZXSlot) /\
        res{1} = (W256.of_int newAggregationChallenge, W256.of_int newAggregatedOpeningAtZ) /\
        (exists (x y: int),
        Primops.memory{1} = UpdateAggregationChallenge105_footprint x y newAggregateAtZXSlot.`1 newAggregateAtZXSlot.`2 currAggregatedAtZOmegaXSlot memory0) /\
        ! Primops.reverted{1}
      )   
    ]. proof.

        proc. inline mload. wp. sp.

        exists* finalCoeff{2}.
        elim*=> val_finalCoeff.

        exists* Primops.memory{1}.
        elim*=>memory1.

        call (pointMulAndAddIntoDest_low_equiv_mid queriesCommitmentPoint.`1 queriesCommitmentPoint.`2 currAggregatedAtZOmegaXSlot.`1 currAggregatedAtZOmegaXSlot.`2 val_finalCoeff queriesCommitmentPoint_addr AGGREGATED_AT_Z_OMEGA_X_SLOT memory1). skip. progress. smt (@Constants). smt (@Constants). smt (). smt (). smt (@Constants). smt (@Constants).
        rewrite /AGGREGATED_AT_Z_OMEGA_X_SLOT Utils.uint256_cast_neg. smt (@Utils).
        rewrite /AGGREGATED_AT_Z_OMEGA_X_SLOT Utils.uint256_cast_add Utils.uint256_cast_neg.
        apply uint256_le_of_le.
        rewrite of_uintK of_uintK of_uintK of_uintK.
        smt (@Utils).
    
        rewrite H29 H30 /PurePrimops.mulmod /PurePrimops.mulmod /PurePrimops.addmod. simplify.
        rewrite of_uintK of_uintK of_uintK of_uintK of_uintK of_uintK of_uintK.
        have ->: (21888242871839275222246405745257275088548364400416034343698204186575808495617 %% W256.modulus) = 21888242871839275222246405745257275088548364400416034343698204186575808495617. smt ().
        have ->: previousCoeff{2} %% W256.modulus = previousCoeff{2}. smt ().
        have ->: currAggregationChallenge{2} %% W256.modulus = currAggregationChallenge{2}. smt ().
        have ->: v_challenge{2} %% W256.modulus = v_challenge{2}. smt ().
        have ->: u_challenge{2} %% W256.modulus = u_challenge{2}. smt ().
        apply uint256_eq_of_eq.
        rewrite Utils.mod_mod_eq_mod. smt (). smt ().
        rewrite Utils.mod_mod_eq_mod. smt (). smt ().
        smt ().

        exists (v_challenge{2} * currAggregationChallenge{2} %% Constants.R).
        exists ((v_challenge{2} * currAggregationChallenge{2} %% Constants.R * valueAtZ_Omega{2} + curAggregatedOpeningAtZ_Omega{2}) %% Constants.R).
        exists (odflt (0, 0) result_R).
        progress.
    
        rewrite H29 /PurePrimops.mulmod. simplify.
        rewrite of_uintK of_uintK.
        apply uint256_eq_of_eq.
        have ->: currAggregationChallenge{2} %% W256.modulus = currAggregationChallenge{2}. smt ().
        have ->: v_challenge{2} %% W256.modulus = v_challenge{2}. smt ().
        have ->: currAggregationChallenge{2} * v_challenge{2} = v_challenge{2} * currAggregationChallenge{2}. smt ().
        rewrite -Constants.R_int.
        reflexivity.

        rewrite H29.
        have ->: (PurePrimops.mload memory_L valueAtZ_Omega{1}) = W256.of_int valueAtZ_Omega{2}.
        have J : exists (x y x' y' : FieldQ.F),
    memory_L =
           (PurePrimops.mstore
              ((PurePrimops.mstore
                  ((PurePrimops.mstore
                      ((PurePrimops.mstore
                          ((PurePrimops.mstore
                              ((PurePrimops.mstore Primops.memory{1} W256.zero
                                  ((W256.of_int ((FieldQ.asint x))%FieldQ))%W256))%PurePrimops
                              ((W256.of_int 32))%W256
                              ((W256.of_int ((FieldQ.asint y))%FieldQ))%W256))%PurePrimops
                          ((W256.of_int 64))%W256
                          ((W256.of_int currAggregatedAtZOmegaXSlot{2}.`1))%W256))%PurePrimops
                      ((W256.of_int 96))%W256
                      ((W256.of_int currAggregatedAtZOmegaXSlot{2}.`2))%W256))%PurePrimops
                  AGGREGATED_AT_Z_OMEGA_X_SLOT
                  ((W256.of_int ((FieldQ.asint x'))%FieldQ))%W256))%PurePrimops
              (AGGREGATED_AT_Z_OMEGA_X_SLOT + (W256.of_int 32)%W256)
              ((W256.of_int ((FieldQ.asint y'))%FieldQ))%W256)%PurePrimops. smt ().
                case J. move => x y x' y' J. rewrite J.
                rewrite load_store_diff. assumption. assumption.
                rewrite load_store_diff. assumption. assumption.
                rewrite load_store_diff. exact Utils.diff_96. exact Utils.diff_neg_96.
                rewrite load_store_diff. exact Utils.diff_64. exact Utils.diff_neg_64.
                rewrite load_store_diff. exact Utils.diff_32. exact Utils.diff_neg_32.
                rewrite load_store_diff. exact Utils.diff_0. exact Utils.diff_neg_0.
                rewrite H31.
                reflexivity.
        rewrite /PurePrimops.addmod /PurePrimops.mulmod /PurePrimops.mulmod. simplify.
        rewrite of_uintK of_uintK of_uintK of_uintK of_uintK of_uintK of_uintK.
        apply uint256_eq_of_eq'.
        have ->: curAggregatedOpeningAtZ_Omega{2} %% W256.modulus = curAggregatedOpeningAtZ_Omega{2}. smt ().
        have ->: currAggregationChallenge{2} %% W256.modulus = currAggregationChallenge{2}. smt ().
        have ->: v_challenge{2} %% W256.modulus = v_challenge{2}. smt ().
        have ->: valueAtZ_Omega{2} %% W256.modulus = valueAtZ_Omega{2}. smt ().
        have ->: 21888242871839275222246405745257275088548364400416034343698204186575808495617 %% W256.modulus = Constants.R. smt ().
        rewrite Utils.mod_mod_eq_mod. smt (). smt ().
        rewrite Utils.mod_mod_eq_mod. smt (). smt ().
        smt ().

        rewrite /UpdateAggregationChallenge105_footprint. simplify.

        have J :
        exists (x y x' y' : FieldQ.F),
    result_R = Some (F_to_int_point (x', y')) /\
    memory_L =
           (PurePrimops.mstore
              ((PurePrimops.mstore
                  ((PurePrimops.mstore
                      ((PurePrimops.mstore
                          ((PurePrimops.mstore
                              ((PurePrimops.mstore Primops.memory{1} W256.zero
                                  ((W256.of_int ((FieldQ.asint x))))))
                              ((W256.of_int 32))
                              ((W256.of_int (FieldQ.asint y)))))
                          ((W256.of_int 64))
                          ((W256.of_int currAggregatedAtZOmegaXSlot{2}.`1))))
                      ((W256.of_int 96))
                      ((W256.of_int currAggregatedAtZOmegaXSlot{2}.`2))))
                  AGGREGATED_AT_Z_OMEGA_X_SLOT
                  ((W256.of_int (FieldQ.asint x')))))
              (AGGREGATED_AT_Z_OMEGA_X_SLOT + (W256.of_int 32))
              ((W256.of_int (FieldQ.asint y')))). smt ().
                case J.
        move=> x y x' y' [J J'].
                exists (FieldQ.asint x).
                exists (FieldQ.asint y).
                rewrite J' J.
                congr.
                have ->: (odflt (0, 0) (Some (F_to_int_point (x', y')))) = F_to_int_point (x', y'). smt ().
                rewrite /F_to_int_point.
                rewrite Utils.proj1 Utils.proj1.
                reflexivity.
                congr.
                have ->: (odflt (0, 0) (Some (F_to_int_point (x', y')))) = F_to_int_point (x', y'). smt ().
            rewrite /F_to_int_point Utils.proj1 Utils.proj2 Utils.proj2. reflexivity.

        smt ().
        smt ().
  qed.
    
