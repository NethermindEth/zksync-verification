pragma Goals:printall.

require        Constants.
require import PointMulAndAddIntoDest.
require import PurePrimops.
require import UInt256.
require import Utils.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

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
  proc mid(queriesCommitmentPoint : int * int, valueAtZ : int, currAggregationChallenge : int, curAggregatedOpeningAtZ : int, v_challenge : int, currAggregatedAtZXSlot : int * int) : (int * int * (int * int)) option = {
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


op UpdateAggregationChallenge_footprint (x y x' y' : int) (currAggregatedAtZXSlot : int * int) (mem_0 : mem) =
  let mem_1 = store mem_0 W256.zero (W256.of_int x) in
  let mem_2 = store mem_1 (W256.of_int 32) (W256.of_int y) in
  let mem_3 = store mem_2 (W256.of_int 64) (W256.of_int currAggregatedAtZXSlot.`1) in
  let mem_4 = store mem_3 (W256.of_int 96) (W256.of_int currAggregatedAtZXSlot.`2) in
  let mem_5 = store mem_4 AGGREGATED_AT_Z_X_SLOT (W256.of_int x') in
  store mem_5 AGGREGATED_AT_Z_Y_SLOT (W256.of_int y').

   

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
    W256.of_int 128 <= valueAtZ_addr /\
    W256.of_int 32 <= -valueAtZ_addr /\
    W256.of_int 32 <= valueAtZ_addr - (AGGREGATED_AT_Z_X_SLOT + W256.of_int 32) /\
    W256.of_int 32 <= AGGREGATED_AT_Z_X_SLOT - valueAtZ_addr /\
    W256.of_int 32 <= valueAtZ_addr - AGGREGATED_AT_Z_X_SLOT /\
    W256.of_int 32 <= (AGGREGATED_AT_Z_X_SLOT + W256.of_int 32) - valueAtZ_addr /\
    arg{1} = (queriesCommitmentPoint_addr, valueAtZ_addr, W256.of_int currAggregationChallenge, W256.of_int curAggregatedOpeningAtZ) /\
    arg{2} = (queriesCommitmentPoint, valueAtZ, currAggregationChallenge, curAggregatedOpeningAtZ, v_challenge, currAggregatedAtZXSlot) /\
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
        res{2} = Some (newAggregationChallenge, newAggregatedOpeningAtZ, newAggregateAtZXSlot) /\
        res{1} = (W256.of_int newAggregationChallenge, W256.of_int newAggregatedOpeningAtZ) /\
        (exists (x y: int),
        Primops.memory{1} = UpdateAggregationChallenge_footprint x y newAggregateAtZXSlot.`1 newAggregateAtZXSlot.`2 currAggregatedAtZXSlot memory0) /\
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
    
        rewrite H25 /PurePrimops.mulmod.
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
        rewrite H25.
        case H56; first last. progress. smt ().
        progress. case H58; first last. progress. smt ().
        progress.
        rewrite load_store_diff. assumption. assumption.
        rewrite load_store_diff. assumption. assumption.
        rewrite load_store_diff. exact diff_96. exact diff_neg_96.
        rewrite load_store_diff. exact diff_64. exact diff_neg_64.
        rewrite load_store_diff. exact diff_32. exact diff_neg_32.
        rewrite load_store_diff. exact diff_0. exact diff_neg_0.
        rewrite H26. rewrite /addmod /mulmod. simplify. rewrite - Constants.R_int.
        do rewrite W256.of_uintK.
        have ->: curAggregatedOpeningAtZ{2} %% W256.modulus = curAggregatedOpeningAtZ{2}. smt ().
        have ->: currAggregationChallenge{2} %% W256.modulus = currAggregationChallenge{2}. smt ().
        have ->: (v_challenge{2} %% W256.modulus) = v_challenge{2}. smt ().
        have ->: (valueAtZ{2} %% W256.modulus) = valueAtZ{2}. smt ().
        rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv).
        rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv).
        congr.
        smt (@IntDiv).
        case H56; first last. progress. smt ().
        progress. case H58; first last. progress. smt ().
        progress. rewrite /UpdateAggregationChallenge_footprint. simplify.
        exists (ZModField.asint x). exists (ZModField.asint y). reflexivity.
        smt ().
        smt ().
    qed.
    

        
