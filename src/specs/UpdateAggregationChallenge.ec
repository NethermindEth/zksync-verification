pragma Goals:printall.

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
  proc mid(queriesCommitmentPoint : int * int, valueAtZ : int, curAggregationChallenge : int, curAggregatedOpeningAtZ : int, v_challenge : int, currAggregatedAtZSlot : int * int) : (int * int * (int * int)) option = {
      var newAggregationChallenge, newAggregatedOpeningAtZ, mNewAggregateAtZXSlot, newAggregateAtZXSlot, ret; 
      newAggregationChallenge <- v_challenge * curAggregationChallenge %% Constants.R;
      mNewAggregateAtZXSlot <@ PointMulAndAddIntoDest.mid(queriesCommitmentPoint.`1, queriesCommitmentPoint.`2, newAggregationChallenge, currAggregatedAtZSlot.`1, currAggregatedAtZSlot.`2);
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

lemma updateAggregationChallenge_equiv_revert : equiv [
    UpdateAggregationChallenge.low ~ UpdateAggregationChallenge.mid :
    Primops.reverted{1} ==> Primops.reverted{1}].    
    proc. inline mload. sp. wp.
    call PointMulAndAddIntoDest_low_equiv_mid_err. skip. progress.
  qed.

lemma updateAggregationChallenge_extracted_equiv_low :
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


op updateAggregationChallenge_footprint (x y x' y' : int) (currAggregatedAtZSlot : int * int) (mem_0 : mem) =
  let mem_1 = store mem_0 W256.zero (W256.of_int x) in
  let mem_2 = store mem_1 (W256.of_int 32) (W256.of_int y) in
  let mem_3 = store mem_2 (W256.of_int 64) (W256.of_int currAggregatedAtZSlot.`1) in
  let mem_4 = store mem_3 (W256.of_int 96) (W256.of_int currAggregatedAtZSlot.`2) in
  let mem_5 = store mem_4 AGGREGATED_AT_Z_X_SLOT (W256.of_int x') in
  store mem_5 AGGREGATED_AT_Z_Y_SLOT (W256.of_int y').

lemma updateAggregationChallenge_low_equiv_mid (queriesCommitmentPoint : int * int) (currAggregatedAtZSlot : int * int) (valueAtZ : int) (curAggregationChallenge : uint256) (curAggregatedOpeningAtZ : uint256) (v_challenge : int) (queriesCommitmentPoint_addr valueAtZ_addr : uint256) (memory0 : MemoryMap.mem) : equiv [
    UpdateAggregationChallenge.low ~ UpdateAggregationChallenge.mid :
    Primops.memory{1} = memory0 /\
    0 <= queriesCommitmentPoint.`1 < Constants.Q /\
    0 <= queriesCommitmentPoint.`2 < Constants.Q /\
    0 <= currAggregatedAtZSlot.`1 < Constants.Q /\
    0 <= currAggregatedAtZSlot.`2 < Constants.Q /\
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
    arg{1} = (queriesCommitmentPoint_addr, valueAtZ_addr, curAggregationChallenge, curAggregatedOpeningAtZ) /\
    arg{2} = (queriesCommitmentPoint, valueAtZ, W256.to_uint curAggregationChallenge, W256.to_uint curAggregatedOpeningAtZ, v_challenge, currAggregatedAtZSlot) /\
    W256.to_uint (PurePrimops.mload memory0 STATE_V_SLOT) = v_challenge /\
    W256.to_uint (PurePrimops.mload memory0 valueAtZ_addr) = valueAtZ /\
    W256.to_uint (PurePrimops.mload memory0 queriesCommitmentPoint_addr) = queriesCommitmentPoint.`1 /\
    W256.to_uint (PurePrimops.mload memory0 (queriesCommitmentPoint_addr + W256.of_int 32)) = queriesCommitmentPoint.`2 /\
    W256.to_uint (PurePrimops.mload memory0  AGGREGATED_AT_Z_X_SLOT) = currAggregatedAtZSlot.`1 /\
    W256.to_uint (PurePrimops.mload memory0 (AGGREGATED_AT_Z_X_SLOT + W256.of_int 32)) = currAggregatedAtZSlot.`2 /\
      !Primops.reverted{1}
      ==>
      (res{2} = None /\ Primops.reverted{1}) \/
      (
        exists (newAggregationChallenge newAggregatedOpeningAtZ : uint256) (newAggregateAtZSlot : FieldQ.F * FieldQ.F),
        res{2} = Some (W256.to_uint newAggregationChallenge, W256.to_uint newAggregatedOpeningAtZ, F_to_int_point newAggregateAtZSlot) /\
        res{1} = (newAggregationChallenge, newAggregatedOpeningAtZ) /\
        (exists (x y: int),
        Primops.memory{1} = updateAggregationChallenge_footprint x y (FieldQ.asint newAggregateAtZSlot.`1) (FieldQ.asint newAggregateAtZSlot.`2) currAggregatedAtZSlot memory0) /\
        ! Primops.reverted{1}
      )   
    ]. proof.
        proc. inline mload. wp. sp.

        exists* newAggregationChallenge{2}.
        elim*=> val_newAggregationChallenge.

        exists* Primops.memory{1}.
        elim*=>memory1.
    
        call (pointMulAndAddIntoDest_low_equiv_mid queriesCommitmentPoint.`1 queriesCommitmentPoint.`2 currAggregatedAtZSlot.`1 currAggregatedAtZSlot.`2 val_newAggregationChallenge queriesCommitmentPoint_addr AGGREGATED_AT_Z_X_SLOT memory1). skip. progress. smt (@Constants). smt (@Constants). smt (@Constants). smt (). smt (@Constants). smt (@Constants). rewrite /AGGREGATED_AT_Z_X_SLOT Utils.uint256_cast_neg. smt (@Utils). rewrite /AGGREGATED_AT_Z_X_SLOT.
        simplify.
        rewrite Utils.uint256_le_of_le Utils.uint256_cast_neg of_uintK of_uintK of_uintK. progress.
        rewrite -H17 to_uintK. reflexivity.
        rewrite -H18 to_uintK. reflexivity.
        rewrite -H19 to_uintK. reflexivity.
        rewrite -H20 to_uintK. reflexivity.
        rewrite /mulmod. simplify.
        rewrite Constants.R_int.
        smt ().
        exists (W256.of_int (W256.to_uint (PurePrimops.mload Primops.memory{1} STATE_V_SLOT) * W256.to_uint curAggregationChallenge{1} %% Constants.R)).
        exists
    (
      W256.of_int
      (
        (to_uint ((PurePrimops.mload Primops.memory{1} STATE_V_SLOT)) *
          to_uint curAggregationChallenge{1} %% Constants.R *
          to_uint ((PurePrimops.mload Primops.memory{1} valueAtZ{1})) +
          to_uint curAggregatedOpeningAtZ{1}) %%
          Constants.R
      )
    ).
        pose r_F := odflt (0, 0) result_R.
    
        exists (FieldQ.inF r_F.`1, FieldQ.inF r_F.`2).
        progress.
        rewrite /addmod /mulmod. simplify. rewrite of_uintK Utils.mod_mod_eq_mod. smt (). smt ().
        reflexivity. 
        rewrite of_uintK.
        pose v_chal := to_uint (PurePrimops.mload Primops.memory{1} STATE_V_SLOT).
        pose cAO := to_uint curAggregatedOpeningAtZ{1}.
        pose cAC := to_uint curAggregationChallenge{1}.
        pose vAZ := W256.to_uint ((PurePrimops.mload Primops.memory{1} valueAtZ{1})).
        rewrite Utils.mod_mod_eq_mod.
        rewrite /Constants.R. progress.
        rewrite /Constants.R. progress.
        reflexivity.

        have J :
    (
      exists (x' y' : FieldQ.F),
      result_R = Some (F_to_int_point (x', y'))
    ). smt ().
        case J. move => x' y' J.
        have ->: r_F = (F_to_int_point (x', y')). smt ().
        rewrite /F_to_int_point. progress. smt (@Field).
        rewrite /F_to_int_point. progress. smt (@Field).
    
        rewrite /addmod /mulmod -Constants.R_int. simplify. rewrite of_uintK of_uintK Utils.mod_mod_eq_mod. smt (). smt ().
        rewrite Utils.mod_mod_eq_mod. smt (). smt ().
        pose v_chal := to_uint (PurePrimops.mload Primops.memory{1} STATE_V_SLOT).
        pose cAO := to_uint curAggregatedOpeningAtZ{1}.
        pose cAC := to_uint curAggregationChallenge{1}.
        pose vAZ := W256.to_uint ((PurePrimops.mload Primops.memory{1} valueAtZ{1})).
        have ->: to_uint ((PurePrimops.mload memory_L valueAtZ{1})) = vAZ.

        have J :
    exists x y x' y',
    memory_L =
    (PurePrimops.mstore
      ((PurePrimops.mstore
          ((PurePrimops.mstore
              ((PurePrimops.mstore
                  ((PurePrimops.mstore
                      ((PurePrimops.mstore Primops.memory{1} W256.zero
                          ((W256.of_int ((FieldQ.asint x))))))
                      ((W256.of_int 32))
                      ((W256.of_int ((FieldQ.asint y))))))
                  ((W256.of_int 64))
                  ((W256.of_int currAggregatedAtZSlot{2}.`1))))
              ((W256.of_int 96))
              ((W256.of_int currAggregatedAtZSlot{2}.`2))))
                AGGREGATED_AT_Z_X_SLOT ((W256.of_int ((FieldQ.asint x'))))))
      (AGGREGATED_AT_Z_X_SLOT + (W256.of_int 32))
      ((W256.of_int ((FieldQ.asint y'))))). smt ().

        case J. progress.
        rewrite load_store_diff. assumption. assumption.
        rewrite load_store_diff. assumption. assumption.
        rewrite load_store_diff. smt (@Utils). smt (@Utils).
        rewrite load_store_diff. smt (@Utils). smt (@Utils).
        rewrite load_store_diff. smt (@Utils). smt (@Utils).
        rewrite load_store_diff. smt (@Utils). smt (@Utils).
        smt ().
        smt (@IntDiv).
        have J :
    (
      exists (x y : FieldQ.F),
      (ecMul_precompile ((FieldQ.inF queriesCommitmentPoint{2}.`1))
        ((FieldQ.inF queriesCommitmentPoint{2}.`2))
        (W256.to_uint ((PurePrimops.mload Primops.memory{1} STATE_V_SLOT)) *
          W256.to_uint curAggregationChallenge{1} %% Constants.R) =
          Some (x, y) /\
        (ConcretePrimops.staticcall_ec_add_should_succeed
          ((W256.of_int ((FieldQ.asint x))),
            (W256.of_int ((FieldQ.asint y))))
          ((W256.of_int currAggregatedAtZSlot{2}.`1),
            (W256.of_int currAggregatedAtZSlot{2}.`2))) /\
              exists (x' y' : FieldQ.F),
              ecAdd_precompile x y ((FieldQ.inF currAggregatedAtZSlot{2}.`1))
        ((FieldQ.inF currAggregatedAtZSlot{2}.`2)) =
          Some (x', y') /\
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
                          ((W256.of_int ((FieldQ.asint y))))))
                      ((W256.of_int 64))
                      ((W256.of_int currAggregatedAtZSlot{2}.`1))))
                  ((W256.of_int 96))
                  ((W256.of_int currAggregatedAtZSlot{2}.`2))))
                    AGGREGATED_AT_Z_X_SLOT ((W256.of_int ((FieldQ.asint x'))))))
          (AGGREGATED_AT_Z_X_SLOT + (W256.of_int 32))
          ((W256.of_int ((FieldQ.asint y')))))
      )
    ). smt ().
        case J. progress. rewrite /updateAggregationChallenge_footprint. simplify. exists (FieldQ.asint x) (FieldQ.asint y).
        congr. congr. smt (@Field). rewrite /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. progress. smt (@Field).
        smt ().
        smt ().
    qed.

        
