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

  proc mid(queriesCommitmentPoint : int * int, valueAtZ_Omega : int, previousCoeff : int, curAggregationChallenge : int, curAggregatedOpeningAtZ_Omega : int, v_challenge : int, u_challenge : int, curAggregatedAtZOmegaXSlot : int * int) : (int * int * (int * int)) option = {
      var newAggregationChallenge, finalCoeff, newAggregatedOpeningAtZ_Omega, mNewAggregateAtZOmegaXSlot, newAggregateAtZOmegaXSlot, ret; 
      newAggregationChallenge <- (v_challenge * curAggregationChallenge) %% Constants.R;
      finalCoeff <- (u_challenge * v_challenge * curAggregationChallenge + previousCoeff) %% Constants.R;
      mNewAggregateAtZOmegaXSlot <@ PointMulAndAddIntoDest.mid(queriesCommitmentPoint.`1, queriesCommitmentPoint.`2, finalCoeff, curAggregatedAtZOmegaXSlot.`1, curAggregatedAtZOmegaXSlot.`2);
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
    

lemma updateAggregationChallenge_105_low_equiv_mid (queriesCommitmentPoint : int * int) (valueAtZ_Omega : int) (previousCoeff : uint256) (curAggregationChallenge : uint256) (curAggregatedOpeningAtZ_Omega : uint256) (v_challenge : int) (u_challenge : int) (curAggregatedAtZOmegaXSlot : int * int) (queriesCommitmentPoint_addr valueAtZOmega_addr : uint256) (memory0 : MemoryMap.mem) : equiv [
    UpdateAggregationChallenge_105.low ~ UpdateAggregationChallenge_105.mid :
    Primops.memory{1} = memory0 /\
    0 <= queriesCommitmentPoint.`1 < Constants.Q /\
    0 <= queriesCommitmentPoint.`2 < Constants.Q /\
    0 <= curAggregatedAtZOmegaXSlot.`1 < Constants.Q /\
    0 <= curAggregatedAtZOmegaXSlot.`2 < Constants.Q /\
    (* 0 <= valueAtZ_Omega < Constants.R /\ *)
    (* 0 <= previousCoeff < Constants.R /\ *)
    (* 0 <= curAggregationChallenge < Constants.R /\ *)
    (* 0 <= curAggregatedOpeningAtZ_Omega < Constants.R /\ *)
    (* 0 <= v_challenge < Constants.R /\ *)
    (* 0 <= u_challenge < Constants.R /\ *)
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
    arg{1} = (queriesCommitmentPoint_addr, valueAtZOmega_addr, previousCoeff, curAggregationChallenge, curAggregatedOpeningAtZ_Omega) /\
    arg{2} = (queriesCommitmentPoint, valueAtZ_Omega, W256.to_uint previousCoeff, W256.to_uint curAggregationChallenge, W256.to_uint curAggregatedOpeningAtZ_Omega, v_challenge, u_challenge, curAggregatedAtZOmegaXSlot) /\
    W256.to_uint (PurePrimops.mload memory0 STATE_V_SLOT) = v_challenge /\
    W256.to_uint (PurePrimops.mload memory0 STATE_U_SLOT) = u_challenge /\
    W256.to_uint (PurePrimops.mload memory0 valueAtZOmega_addr) = valueAtZ_Omega /\
    W256.to_uint (PurePrimops.mload memory0 queriesCommitmentPoint_addr) = queriesCommitmentPoint.`1 /\
    W256.to_uint (PurePrimops.mload memory0 (queriesCommitmentPoint_addr + W256.of_int 32)) = queriesCommitmentPoint.`2 /\
    W256.to_uint (PurePrimops.mload memory0  AGGREGATED_AT_Z_OMEGA_X_SLOT) = curAggregatedAtZOmegaXSlot.`1 /\
    W256.to_uint (PurePrimops.mload memory0 (AGGREGATED_AT_Z_OMEGA_X_SLOT + W256.of_int 32)) = curAggregatedAtZOmegaXSlot.`2 /\
      !Primops.reverted{1}
      ==>
      (res{2} = None /\ Primops.reverted{1}) \/
      (
        exists (newAggregationChallenge newAggregatedOpeningAtZ : int) (newAggregateAtZXSlot : int * int),
        res{2} = Some (newAggregationChallenge, newAggregatedOpeningAtZ, newAggregateAtZXSlot) /\
        res{1} = (W256.of_int newAggregationChallenge, W256.of_int newAggregatedOpeningAtZ) /\
        (exists (x y: int),
        Primops.memory{1} = UpdateAggregationChallenge105_footprint x y newAggregateAtZXSlot.`1 newAggregateAtZXSlot.`2 curAggregatedAtZOmegaXSlot memory0) /\
        ! Primops.reverted{1}
      )   
    ]. proof.

        proc. inline mload. wp. sp.

        exists* finalCoeff{2}.
        elim*=> val_finalCoeff.

        exists* Primops.memory{1}.
        elim*=>memory1.

        call (pointMulAndAddIntoDest_low_equiv_mid queriesCommitmentPoint.`1 queriesCommitmentPoint.`2 curAggregatedAtZOmegaXSlot.`1 curAggregatedAtZOmegaXSlot.`2 val_finalCoeff queriesCommitmentPoint_addr AGGREGATED_AT_Z_OMEGA_X_SLOT memory1). skip. progress. smt (@Constants). smt (@Constants). smt (). smt (). smt (@Constants). smt (@Constants).
        rewrite /AGGREGATED_AT_Z_OMEGA_X_SLOT Utils.uint256_cast_neg of_uintK. progress.
        rewrite /AGGREGATED_AT_Z_OMEGA_X_SLOT Utils.uint256_cast_neg. progress.

        rewrite -H17 to_uintK. reflexivity.
        rewrite -H18 to_uintK. reflexivity.
        rewrite -H19 to_uintK. reflexivity.
        rewrite -H20 to_uintK. reflexivity.
    
        rewrite /PurePrimops.mulmod /PurePrimops.mulmod /PurePrimops.addmod. simplify. rewrite -Constants.R_int of_uintK of_uintK.
        rewrite mod_mod_eq_mod. smt (). smt ().
        rewrite mod_mod_eq_mod. smt (). smt ().
        congr. smt (@Utils).

        exists (to_uint (PurePrimops.mload Primops.memory{1} STATE_V_SLOT) * to_uint curAggregationChallenge{1} %% Constants.R).
        exists
    (
      (to_uint (PurePrimops.mload Primops.memory{1} STATE_V_SLOT) *
        to_uint curAggregationChallenge{1} %% Constants.R *
        to_uint (PurePrimops.mload Primops.memory{1} valueAtZ_Omega{1}) +
        to_uint curAggregatedOpeningAtZ_Omega{1}) %%
        Constants.R
    ).
        exists (odflt (0, 0) result_R).
        progress.
    
        rewrite /PurePrimops.mulmod -Constants.R_int. simplify.
        congr. smt ().

        rewrite /PurePrimops.mulmod /PurePrimops.mulmod /PurePrimops.addmod. simplify. rewrite -Constants.R_int of_uintK of_uintK.
        rewrite mod_mod_eq_mod. smt (). smt ().
        rewrite mod_mod_eq_mod. smt (). smt ().
        have ->: to_uint (PurePrimops.mload memory_L valueAtZ_Omega{1}) = to_uint (PurePrimops.mload Primops.memory{1} valueAtZ_Omega{1}).
        have J :
    (
      exists (x y : FieldQ.F),
      ecMul_precompile ((FieldQ.inF queriesCommitmentPoint{2}.`1))
        ((FieldQ.inF queriesCommitmentPoint{2}.`2))
        ((W256.to_uint ((PurePrimops.mload Primops.memory{1} STATE_U_SLOT)) *
          W256.to_uint ((PurePrimops.mload Primops.memory{1} STATE_V_SLOT)) *
          W256.to_uint curAggregationChallenge{1} + W256.to_uint previousCoeff{1}) %%
          Constants.R) =
          Some (x, y) /\
        (ConcretePrimops.staticcall_ec_add_should_succeed
          ((W256.of_int ((FieldQ.asint x))),
            (W256.of_int ((FieldQ.asint y))))
          ((W256.of_int curAggregatedAtZOmegaXSlot{2}.`1),
            (W256.of_int curAggregatedAtZOmegaXSlot{2}.`2))) /\
              exists (x' y' : FieldQ.F),
              ecAdd_precompile x y
        ((FieldQ.inF curAggregatedAtZOmegaXSlot{2}.`1))
        ((FieldQ.inF curAggregatedAtZOmegaXSlot{2}.`2)) =
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
                      ((W256.of_int curAggregatedAtZOmegaXSlot{2}.`1))))
                  ((W256.of_int 96))
                  ((W256.of_int curAggregatedAtZOmegaXSlot{2}.`2))))
                    AGGREGATED_AT_Z_OMEGA_X_SLOT
              ((W256.of_int ((FieldQ.asint x'))))))
          (AGGREGATED_AT_Z_OMEGA_X_SLOT + (W256.of_int 32))
          ((W256.of_int ((FieldQ.asint y')))))
      ). smt ().
          case J. move => x y [J1 [J2 J3]]. case J3. move => x' y' [J3 [J4 J5]]. rewrite J5.
          rewrite /AGGREGATED_AT_Z_OMEGA_X_SLOT.
          do 3! (rewrite load_store_diff; progress).
          smt (@Utils).
          smt (@Utils).
          rewrite load_store_diff. smt (@Utils). smt (@Utils).
          rewrite load_store_diff. smt (@Utils). smt (@Utils).
          rewrite load_store_diff. smt (@Utils). smt (@Utils).
          reflexivity.
      
        smt (@Utils).

        have J :
    (
      exists (x y : FieldQ.F),
        ecMul_precompile ((FieldQ.inF queriesCommitmentPoint{2}.`1))
           ((FieldQ.inF queriesCommitmentPoint{2}.`2))
           ((to_uint (PurePrimops.mload Primops.memory{1} STATE_U_SLOT) *
             to_uint (PurePrimops.mload Primops.memory{1} STATE_V_SLOT) *
             to_uint curAggregationChallenge{1} + to_uint previousCoeff{1}) %%
            Constants.R) =
         Some (x, y) /\
         (ConcretePrimops.staticcall_ec_add_should_succeed
            ((W256.of_int ((FieldQ.asint x))),
             (W256.of_int ((FieldQ.asint y))))
            ((W256.of_int curAggregatedAtZOmegaXSlot{2}.`1),
             (W256.of_int curAggregatedAtZOmegaXSlot{2}.`2))) /\
         exists (x' y' : FieldQ.F),
           ecAdd_precompile x y
             ((FieldQ.inF curAggregatedAtZOmegaXSlot{2}.`1))
             ((FieldQ.inF curAggregatedAtZOmegaXSlot{2}.`2)) =
           Some (x', y') /\
           result_R = Some (F_to_int_point (x', y')) /\
           memory_L =
           PurePrimops.mstore
             (PurePrimops.mstore
                (PurePrimops.mstore
                   (PurePrimops.mstore
                      (PurePrimops.mstore
                         (PurePrimops.mstore Primops.memory{1} W256.zero
                            ((W256.of_int ((FieldQ.asint x)))))
                         ((W256.of_int 32))
                         ((W256.of_int ((FieldQ.asint y)))))
                      ((W256.of_int 64))
                      ((W256.of_int curAggregatedAtZOmegaXSlot{2}.`1)))
                   ((W256.of_int 96))
                   ((W256.of_int curAggregatedAtZOmegaXSlot{2}.`2)))
                AGGREGATED_AT_Z_OMEGA_X_SLOT
                ((W256.of_int ((FieldQ.asint x')))))
             (AGGREGATED_AT_Z_OMEGA_X_SLOT + (W256.of_int 32))
             ((W256.of_int ((FieldQ.asint y'))))
           ). smt ().
               case J. move=> x y [J1 [J2 J3]]. case J3. move => x' y' [J3 [J4 J5]]. rewrite /UpdateAggregationChallenge105_footprint J4 /F_to_int_point. progress. exists (FieldQ.asint x) (FieldQ.asint y). exact J5.
               smt ().
               smt ().
  qed.
    
