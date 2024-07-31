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
    arg{1} = (queriesCommitmentPoint_addr, valueAtZ_addr, W256.of_int currAggregationChallenge, W256.of_int curAggregatedOpeningAtZ) /\
    arg{2} = (queriesCommitmentPoint, currAggregatedAtZXSlot, valueAtZ, currAggregationChallenge, curAggregatedOpeningAtZ, v_challenge) /\
    PurePrimops.mload memory0 STATE_V_SLOT = W256.of_int v_challenge /\
    PurePrimops.mload memory0 valueAtZ_addr = W256.of_int valueAtZ /\
    PurePrimops.mload memory0 queriesCommitmentPoint_addr = W256.of_int queriesCommitmentPoint.`1 /\
    PurePrimops.mload memory0 (queriesCommitmentPoint_addr + W256.of_int 32) = W256.of_int queriesCommitmentPoint.`2 /\
    PurePrimops.mload memory0 AGGREGATED_AT_Z_X_SLOT = W256.of_int currAggregatedAtZXSlot.`1 /\
    PurePrimops.mload memory0 (AGGREGATED_AT_Z_X_SLOT + W256.of_int 32) = W256.of_int currAggregatedAtZXSlot.`2 
      ==>
      (res{2} = None) \/
      (
        exists (newAggregationChallenge newAggregatedOpeningAtZ : int) (newAggregateAtZXSlot : int * int),
        newAggregationChallenge = v_challenge * currAggregationChallenge %% Constants.R /\
        newAggregatedOpeningAtZ = (v_challenge * currAggregationChallenge * valueAtZ + curAggregatedOpeningAtZ) %% Constants.R /\
        res{2} = Some (newAggregationChallenge, newAggregatedOpeningAtZ, newAggregateAtZXSlot))
    ]. proof.
        proc. inline mload. wp. sp.

        exists* newAggregationChallenge{2}.
        elim*=> val_newAggregationChallenge.

        exists* Primops.memory{1}.
        elim*=>memory1.
    
        call (PointMulAndAddIntoDest_mid_of_low queriesCommitmentPoint.`1 queriesCommitmentPoint.`2 currAggregatedAtZXSlot.`1 currAggregatedAtZXSlot.`2 val_newAggregationChallenge queriesCommitmentPoint_addr AGGREGATED_AT_Z_X_SLOT memory1). skip. progress.
    
