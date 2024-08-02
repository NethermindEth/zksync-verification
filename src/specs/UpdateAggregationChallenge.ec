require        Constants.
require import PointMulAndAddIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module UpdateAggregationChallenge = {
  proc low(queriesCommitmentPoint : uint256, valueAtZ : uint256, curAggregationChallenge : uint256, curAggregatedOpeningAtZ : uint256): (uint256 * uint256) = {
    var newAggregationChallenge, newAggregatedOpeningAtZ, _3, _5, _6;
    _3 <@ Primops.mload(STATE_V_SLOT);
    newAggregationChallenge <- (PurePrimops.mulmod curAggregationChallenge _3 R_MOD);
    PointMulAndAddIntoDest.low(queriesCommitmentPoint, newAggregationChallenge, AGGREGATED_AT_Z_X_SLOT);
    _5 <@ Primops.mload(valueAtZ);
    _6 <- (PurePrimops.mulmod newAggregationChallenge _5 R_MOD);
    newAggregatedOpeningAtZ <- (PurePrimops.addmod curAggregatedOpeningAtZ _6 R_MOD);
    return (newAggregationChallenge, newAggregatedOpeningAtZ);
  }
      proc mid(queriesCommitmentPoint : int * int, currAggregatedAtZXSlot : int * int, valueAtZ : int, currAggregationChallenge : int, curAggregatedOpeningAtZ : int, v_challenge : int) : (int * int * (int * int)) option = {
      var newAggregationChallenge, newAggregatedOpeningAtZ, mNewAggregateAtZXSlot, newAggregateAtZXSlot, ret; 
      newAggregationChallenge <- v_challenge * currAggregationChallenge %% Constants.R;
      mNewAggregateAtZXSlot <@ PointMulAndAddIntoDest.mid(queriesCommitmentPoint.`1, queriesCommitmentPoint.`2, newAggregationChallenge, currAggregatedAtZXSlot.`1, currAggregatedAtZXSlot.`2);
      if (is_some mNewAggregateAtZXSlot) {
        newAggregateAtZXSlot <- odflt (0, 0) mNewAggregateAtZXSlot;
        newAggregatedOpeningAtZ <- (newAggregationChallenge * valueAtZ + curAggregatedOpeningAtZ) %% Constants.R;
        ret   <- Some (newAggregationChallenge, newAggregatedOpeningAtZ, newAggregateAtZXSlot);
      } else {
          ret <- None;
      }
      return ret;
  }
}.

op UpdateAggregationChallenge_footprint (x y x' y' : F) (currAggregatedAtZXSlot : int * int) (memory0 : MemoryMap.mem) =
           (PurePrimops.mstore
              ((PurePrimops.mstore
                  ((PurePrimops.mstore
                      ((PurePrimops.mstore
                          ((PurePrimops.mstore
                              (PurePrimops.mstore memory0 W256.zero
                                  ((of_int (ZModField.asint x)))%W256)
                              ((of_int 32))%W256
                              ((of_int (ZModField.asint y)))%W256))
                          ((of_int 64))%W256
                          ((W256.of_int currAggregatedAtZXSlot.`1))%W256))%PurePrimops
                      ((of_int 96))%W256
                      ((of_int currAggregatedAtZXSlot.`2))%W256))%PurePrimops
                  AGGREGATED_AT_Z_X_SLOT
                  ((of_int (ZModField.asint x')))%W256))%PurePrimops
              (AGGREGATED_AT_Z_X_SLOT + (of_int 32)%W256)
              ((of_int (ZModField.asint y')%ZModField))%W256)%PurePrimops.

lemma UpdateAggregationChallenge_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_updateAggregationChallenge ~ UpdateAggregationChallenge.low :
      ={arg, glob UpdateAggregationChallenge} ==>
      ={res, glob UpdateAggregationChallenge}
    ].
proof.
  proc.
  inline Primops.mload. wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  skip. rewrite /Constants.R. by progress.
qed.

lemma UpdateAggregationChallenge_mid_of_low (queriesCommitmentPoint : int * int) (currAggregatedAtZXSlot : int * int) (valueAtZ : int) (currAggregationChallenge : int) (curAggregatedOpeningAtZ : int) (v_challenge : int) (queriesCommitmentPoint_addr valueAtZ_addr : uint256) (memory0 : MemoryMap.mem) : equiv [
    UpdateAggregationChallenge.low ~ UpdateAggregationChallenge.mid :
    Primops.memory{1} = memory0 /\
    0 <= queriesCommitmentPoint.`1 < Constants.Q /\
    0 <= queriesCommitmentPoint.`2 < Constants.Q /\
    0 <= currAggregatedAtZXSlot.`1 < Constants.Q /\
    0 <= currAggregatedAtZXSlot.`2 < Constants.Q /\
    0 <= valueAtZ < Constants.R /\
    0 <= currAggregationChallenge < Constants.R /\
    0 <= curAggregatedOpeningAtZ < Constants.R /\
    0 <= v_challenge < Constants.R /\
    W256.of_int 128 <= queriesCommitmentPoint_addr /\
    W256.of_int 64 <= - queriesCommitmentPoint_addr /\
    W256.of_int 128 <= queriesCommitmentPoint_addr + W256.of_int 32 /\
    W256.of_int 32 <= - (queriesCommitmentPoint_addr + W256.of_int 32) /\
    arg{1} = (queriesCommitmentPoint_addr, valueAtZ_addr, W256.of_int currAggregationChallenge, W256.of_int curAggregatedOpeningAtZ) /\
    arg{2} = (queriesCommitmentPoint, currAggregatedAtZXSlot, valueAtZ, currAggregationChallenge, curAggregatedOpeningAtZ, v_challenge) /\
    PurePrimops.mload memory0 STATE_V_SLOT = W256.of_int v_challenge /\
    PurePrimops.mload memory0 valueAtZ_addr = W256.of_int valueAtZ /\
    PurePrimops.mload memory0 queriesCommitmentPoint_addr = W256.of_int queriesCommitmentPoint.`1 /\
    PurePrimops.mload memory0 (queriesCommitmentPoint_addr + W256.of_int 32) = W256.of_int queriesCommitmentPoint.`2 /\
    PurePrimops.mload memory0  AGGREGATED_AT_Z_X_SLOT = W256.of_int currAggregatedAtZXSlot.`1 /\
    PurePrimops.mload memory0 (AGGREGATED_AT_Z_X_SLOT + W256.of_int 32) = W256.of_int currAggregatedAtZXSlot.`2 /\
      !Primops.reverted{1}
      ==>
      (res{2} = None /\ Primops.reverted{1}) \/
      (
        exists (newAggregationChallenge newAggregatedOpeningAtZ : int) (newAggregateAtZXSlot : int * int),
        (* newAggregationChallenge = v_challenge * currAggregationChallenge %% Constants.R /\ *)
        (* newAggregatedOpeningAtZ = (v_challenge * currAggregationChallenge * valueAtZ + curAggregatedOpeningAtZ) %% Constants.R /\ *)
        res{2} = Some (newAggregationChallenge, newAggregatedOpeningAtZ, newAggregateAtZXSlot) /\
        res{1} = (W256.of_int newAggregationChallenge, W256.of_int newAggregatedOpeningAtZ) /\
        (* Primops.memory{1} = UpdateAggregationChallenge_footprint queriesCommitmentPoint{2}.`1 queriesCommitmentPoint{2}.`2 /\ *)
        Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore memory0 AGGREGATED_AT_Z_X_SLOT (W256.of_int newAggregateAtZXSlot.`1)) (AGGREGATED_AT_Z_X_SLOT + W256.of_int 32) (W256.of_int newAggregateAtZXSlot.`2) /\
        ! Primops.reverted{1}
      )
    
      
    ]. proof.
        proc. inline mload. wp. sp.

        exists* newAggregationChallenge{2}.
        elim*=> val_newAggregationChallenge.

        exists* Primops.memory{1}.
        elim*=>memory1.
    
        call (PointMulAndAddIntoDest_mid_of_low queriesCommitmentPoint.`1 queriesCommitmentPoint.`2 currAggregatedAtZXSlot.`1 currAggregatedAtZXSlot.`2 val_newAggregationChallenge queriesCommitmentPoint_addr AGGREGATED_AT_Z_X_SLOT memory1). skip. progress. smt (). smt (). smt (). smt (). smt (). smt (). rewrite /AGGREGATED_AT_Z_X_SLOT Utils.uint256_cast_neg. smt (@Utils). rewrite /AGGREGATED_AT_Z_X_SLOT.
        have ->: 512 + 1312 + 1568 + 128 + 704 + 256 + 0 = 4480. smt ().
        have ->: 4480 %% W256.modulus = 4480. smt ().
        have ->: (of_int 4480)%W256 + (of_int 32)%W256 = W256.of_int 4512. smt ().
        rewrite Utils.uint256_le_of_le Utils.uint256_cast_neg of_uintK.
        have ->: 32 %% W256.modulus = 32. smt ().
        have ->: (- to_uint ((of_int 4512))%W256) = - 4512. smt ().
        have ->: (-4512) %% W256.modulus = W256.modulus - 4512. smt ().
        rewrite of_uintK.
        smt ().
    
        rewrite H19 /PurePrimops.mulmod.
        simplify.
        rewrite of_uintK.
        have ->: to_uint R_MOD = Constants.R. smt (@Constants).
        have ->: currAggregationChallenge{2} %% W256.modulus = currAggregationChallenge{2}.
        rewrite Utils.mod_eq_self. smt (). smt ().  smt (). reflexivity. rewrite of_uintK.
        have ->: (v_challenge{2} %% W256.modulus) = v_challenge{2}. smt ().
        smt ().
        exists (v_challenge{2} * currAggregationChallenge{2} %% Constants.R).
        exists ((v_challenge{2} * currAggregationChallenge{2} %% Constants.R * valueAtZ{2} + curAggregatedOpeningAtZ{2}) %% Constants.R).
        exists (odflt (0, 0) result_R).
        progress.
        rewrite H19.
        have ->: PurePrimops.mload memory_L valueAtZ{1} = W256.of_int valueAtZ{2}. admit.
        rewrite /PurePrimops.addmod /PurePrimops.mulmod.
        simplify.
        rewrite /PurePrimops.mulmod. simplify.
        rewrite of_uintK of_uintK of_uintK of_uintK of_uintK of_uintK of_uintK.
        have ->: curAggregatedOpeningAtZ{2} %% W256.modulus = curAggregatedOpeningAtZ{2}. smt ().
        have ->: currAggregationChallenge{2} %% W256.modulus = currAggregationChallenge{2}. smt ().
        have ->: (v_challenge{2} %% W256.modulus) = v_challenge{2}. smt ().
        have ->: (valueAtZ{2} %% W256.modulus) = valueAtZ{2}. smt ().
        have ->: (21888242871839275222246405745257275088548364400416034343698204186575808495617 %%
        W256.modulus) = Constants.R. smt ().
        congr.
        rewrite Utils.mod_mod_eq_mod. smt (). smt ().
        rewrite Utils.mod_mod_eq_mod. smt (). smt ().
        smt ().
        admit. smt (). smt ().
    qed.
    

        
