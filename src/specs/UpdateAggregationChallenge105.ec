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

    proc high_encapsulated(queriesCommitmentPoint : g, valueAtZ_Omega : FieldR.F, previousCoeff : FieldR.F, curAggregationChallenge : FieldR.F, curAggregatedOpeningAtZ_Omega : FieldR.F, v_challenge : FieldR.F, u_challenge : FieldR.F, curAggregatedAtZOmegaXSlot : g) : (FieldR.F * FieldR.F * g) = {
        var newAggregationChallenge, finalCoeff, newAggregatedOpeningAtZ_Omega; 
        newAggregationChallenge <- v_challenge * curAggregationChallenge;
        finalCoeff <- u_challenge * v_challenge * curAggregationChallenge + previousCoeff;
        curAggregatedAtZOmegaXSlot <@ PointMulAndAddIntoDest.high(queriesCommitmentPoint, finalCoeff, curAggregatedAtZOmegaXSlot);
        newAggregatedOpeningAtZ_Omega <- newAggregationChallenge * valueAtZ_Omega + curAggregatedOpeningAtZ_Omega;
        return (newAggregationChallenge, newAggregatedOpeningAtZ_Omega, curAggregatedAtZOmegaXSlot);
    }

    proc high(queriesCommitmentPoint : g, valueAtZ_Omega : FieldR.F, previousCoeff : FieldR.F, curAggregationChallenge : FieldR.F, curAggregatedOpeningAtZ_Omega : FieldR.F, v_challenge : FieldR.F, u_challenge : FieldR.F, curAggregatedAtZOmegaXSlot : g) : (FieldR.F * FieldR.F * g) = {
        var newAggregationChallenge, finalCoeff, newAggregatedOpeningAtZ_Omega; 
        newAggregationChallenge <- v_challenge * curAggregationChallenge;
        finalCoeff <- u_challenge * v_challenge * curAggregationChallenge + previousCoeff;
        curAggregatedAtZOmegaXSlot <- finalCoeff * queriesCommitmentPoint + curAggregatedAtZOmegaXSlot;
        newAggregatedOpeningAtZ_Omega <- newAggregationChallenge * valueAtZ_Omega + curAggregatedOpeningAtZ_Omega;
        return (newAggregationChallenge, newAggregatedOpeningAtZ_Omega, curAggregatedAtZOmegaXSlot);
    }
    
}.

lemma updateAggregationChallenge_105_equiv_revert : equiv [
    UpdateAggregationChallenge_105.low ~ UpdateAggregationChallenge_105.mid :
    Primops.reverted{1} ==> Primops.reverted{1}].    
    proc. inline mload. sp. wp.

    call PointMulAndAddIntoDest_low_equiv_mid_err. skip. progress.
  qed.

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

op updateAggregationChallenge105_footprint (x y x' y' : int) (currAggregatedAtZXSlot : int * int) (mem_0 : mem) =
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
        exists (newAggregationChallenge newAggregatedOpeningAtZ : uint256) (newAggregateAtZXSlot : FieldQ.F * FieldQ.F),
        res{2} = Some (W256.to_uint newAggregationChallenge, W256.to_uint newAggregatedOpeningAtZ, F_to_int_point newAggregateAtZXSlot) /\
        res{1} = (newAggregationChallenge, newAggregatedOpeningAtZ) /\
        (exists (x y: int),
        Primops.memory{1} = updateAggregationChallenge105_footprint x y (FieldQ.asint newAggregateAtZXSlot.`1) (FieldQ.asint newAggregateAtZXSlot.`2) curAggregatedAtZOmegaXSlot memory0) /\
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

        exists (W256.of_int (to_uint (PurePrimops.mload Primops.memory{1} STATE_V_SLOT) * to_uint curAggregationChallenge{1} %% Constants.R)).
        exists
    (W256.of_int 
      (
        (to_uint (PurePrimops.mload Primops.memory{1} STATE_V_SLOT) *
          to_uint curAggregationChallenge{1} %% Constants.R *
          to_uint (PurePrimops.mload Primops.memory{1} valueAtZ_Omega{1}) +
          to_uint curAggregatedOpeningAtZ_Omega{1}) %%
          Constants.R
      )
    ).
        pose r_F := odflt (0, 0) result_R.
    
        exists (FieldQ.inF r_F.`1, FieldQ.inF r_F.`2).
        progress.
    
        rewrite of_uintK Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. smt (). reflexivity.
        rewrite of_uintK Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. smt (). reflexivity.

        have J :
    (
      exists (x y x' y' : FieldQ.F),
      ecAdd_precompile x y
      ((FieldQ.inF curAggregatedAtZOmegaXSlot{2}.`1))
      ((FieldQ.inF curAggregatedAtZOmegaXSlot{2}.`2)) =
        Some (x', y') /\
      result_R = Some (F_to_int_point (x', y')) 
    ). smt ().
        case J. progress.
        have ->: r_F = odflt (0, 0) (Some (F_to_int_point (x', y'))). smt ().
        rewrite /F_to_int_point. simplify.
        rewrite FieldQ.inFK FieldQ.inFK modz_small.
        progress.
        exact FieldQ.ge0_asint.
        have ->: `|FieldQ.p| = FieldQ.p. smt ().
        exact FieldQ.gtp_asint.
        rewrite modz_small.
        progress.
        exact FieldQ.ge0_asint.
        have ->: `|FieldQ.p| = FieldQ.p. smt ().
        exact FieldQ.gtp_asint.
        progress.

        rewrite /mulmod -Constants.R_int. simplify.
        smt ().

        rewrite /mulmod /addmod -Constants.R_int. simplify.
        rewrite of_uintK of_uintK Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. smt ().
        rewrite Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. smt ().

        rewrite -modzDm.
        rewrite -(modzDm _ (to_uint curAggregatedOpeningAtZ_Omega{1})).
        rewrite -modzMm.
        rewrite -(modzMm (to_uint curAggregationChallenge{1})).
        rewrite -(modzMm _ (to_uint ((PurePrimops.mload Primops.memory{1} valueAtZ_Omega{1})))).
        rewrite -(modzMm _ (to_uint curAggregationChallenge{1})).
        rewrite mod_mod_eq_mod' mod_mod_eq_mod' mod_mod_eq_mod'.
        have ->: PurePrimops.mload memory_L valueAtZ_Omega{1} = PurePrimops.mload Primops.memory{1} valueAtZ_Omega{1}.
        have J :
    (
      exists (x y x' y' : FieldQ.F),
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
              case J. progress.
              do 2! (rewrite load_store_diff; try assumption).
              rewrite load_store_diff. smt (@Utils). smt (@Utils).
              rewrite load_store_diff. smt (@Utils). smt (@Utils).
              rewrite load_store_diff. smt (@Utils). smt (@Utils).
              rewrite load_store_diff. smt (@Utils). smt (@Utils).
              reflexivity.
              smt (@IntDiv).
              case H46. move => [J J'].
              case J'. move => x y J'.
              case J'. move => [J0 [J1 J2]].
              case J2. move => x' y' [J2 [J3 [J4]]] NR.
              rewrite J4.
              have ->: r_F = odflt (0, 0) result_R. smt ().
              rewrite /UpdateAggregationChallenge105_footprint. simplify.
              exists (FieldQ.asint x) (FieldQ.asint y).
              rewrite J3 /F_to_int_point. simplify.
              rewrite FieldQ.asintK FieldQ.asintK. reflexivity.
              smt ().
              smt ().
              smt ().
              smt ().
        qed.

lemma updateAggregationChallenge_105_mid_equiv_high_encapsulated :
equiv [
    UpdateAggregationChallenge_105.mid ~ UpdateAggregationChallenge_105.high_encapsulated :
      arg{1} = (F_to_int_point (aspoint_G1 queriesCommitmentPoint{2}), FieldR.asint valueAtZ_Omega{2}, FieldR.asint previousCoeff{2}, FieldR.asint curAggregationChallenge{2}, FieldR.asint curAggregatedOpeningAtZ_Omega{2}, FieldR.asint v_challenge{2}, FieldR.asint u_challenge{2}, F_to_int_point (aspoint_G1 curAggregatedAtZOmegaXSlot{2})) ==>
      res{1} = Some (FieldR.asint res{2}.`1, FieldR.asint res{2}.`2, F_to_int_point (aspoint_G1 res{2}.`3))
    ]. proof.
        proc. wp. sp.
        call pointMulAndAddIntoDest_mid_equiv_high. skip. progress.
        rewrite FieldR.addE FieldR.mulE FieldR.mulE -Constants.r_eq_fieldr_p. smt (@IntDiv).
        rewrite FieldR.mulE -Constants.r_eq_fieldr_p. reflexivity.
        rewrite FieldR.addE FieldR.mulE FieldR.mulE -Constants.r_eq_fieldr_p. smt (@IntDiv).
  qed.
    
lemma updateAggregationChallenge_105_mid_equiv_high :
equiv [
    UpdateAggregationChallenge_105.mid ~ UpdateAggregationChallenge_105.high :
      arg{1} = (F_to_int_point (aspoint_G1 queriesCommitmentPoint{2}), FieldR.asint valueAtZ_Omega{2}, FieldR.asint previousCoeff{2}, FieldR.asint curAggregationChallenge{2}, FieldR.asint curAggregatedOpeningAtZ_Omega{2}, FieldR.asint v_challenge{2}, FieldR.asint u_challenge{2}, F_to_int_point (aspoint_G1 curAggregatedAtZOmegaXSlot{2})) ==>
      res{1} = Some (FieldR.asint res{2}.`1, FieldR.asint res{2}.`2, F_to_int_point (aspoint_G1 res{2}.`3))
    ]. proof.
    transitivity UpdateAggregationChallenge_105.high_encapsulated
    (
      arg{1} = (F_to_int_point (aspoint_G1 queriesCommitmentPoint{2}), FieldR.asint valueAtZ_Omega{2}, FieldR.asint previousCoeff{2}, FieldR.asint curAggregationChallenge{2}, FieldR.asint curAggregatedOpeningAtZ_Omega{2}, FieldR.asint v_challenge{2}, FieldR.asint u_challenge{2}, F_to_int_point (aspoint_G1 curAggregatedAtZOmegaXSlot{2})) ==>
      res{1} = Some (FieldR.asint res{2}.`1, FieldR.asint res{2}.`2, F_to_int_point (aspoint_G1 res{2}.`3))
    ) (={arg} ==> ={res}).
        progress.
        exists arg{2}. by progress.
        by progress.
        exact updateAggregationChallenge_105_mid_equiv_high_encapsulated.
        proc.
        inline PointMulAndAddIntoDest.high. wp. skip. progress.
  qed.
