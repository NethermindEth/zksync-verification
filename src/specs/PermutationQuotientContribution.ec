pragma Goals:printall.

require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.
require import Utils.
require import VerifierConsts.

module PermutationQuotientContribution = {
  proc low(): uint256 = {
    var _res, tmp270, tmp271, _gamma, _beta, _factorMultiplier, tmp274, tmp275, tmp276, tmp277, tmp278, tmp279, tmp280, _22, _l0AtZ, tmp282, _26;
    tmp270 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    tmp271 <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    _res <- (PurePrimops.mulmod tmp271 tmp270 R_MOD);
    _gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    _beta <@ Primops.mload(STATE_BETA_SLOT);
    tmp274 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.mulmod tmp274 _beta R_MOD);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma R_MOD);
    tmp275 <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier tmp275 R_MOD);
    _res <- (PurePrimops.mulmod _res _factorMultiplier R_MOD);
    tmp276 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.mulmod tmp276 _beta R_MOD);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma R_MOD);
    tmp277 <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier tmp277 R_MOD);
    _res <- (PurePrimops.mulmod _res _factorMultiplier R_MOD);
    tmp278 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.mulmod tmp278 _beta R_MOD);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma R_MOD);
    tmp279 <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier tmp279 R_MOD);
    _res <- (PurePrimops.mulmod _res _factorMultiplier R_MOD);
    tmp280 <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    _22 <- (PurePrimops.addmod tmp280 _gamma R_MOD);
    _res <- (PurePrimops.mulmod _res _22 R_MOD);
    _res <- (R_MOD - _res);
    _l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    tmp282 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    _l0AtZ <- (PurePrimops.mulmod _l0AtZ tmp282 R_MOD);
    _26 <- (R_MOD - _l0AtZ);
    _res <- (PurePrimops.addmod _res _26 R_MOD);
    return _res;
  }

  proc mid(
    statePowerOfAlpha4Slot
    statePowerOfAlpha5Slot
    proofCopyPermutationGrandProductOpeningAtZOmegaSlot
    stateBetaSlot
    stateGammaSlot
    proofCopyPermutationPolys0OpeningAtZSlot
    proofCopyPermutationPolys1OpeningAtZSlot
    proofCopyPermutationPolys2OpeningAtZSlot
    proofStatePolys0OpeningAtZSlot
    proofStatePolys1OpeningAtZSlot
    proofStatePolys2OpeningAtZSlot
    proofStatePolys3OpeningAtZSlot
    stateL0AtZSlot : int
  ) : int = {
    var s0BGa, s1BGb, s2BGc, s3G, inv1, inv2;
    
    s0BGa <- (proofCopyPermutationPolys0OpeningAtZSlot * stateBetaSlot + stateGammaSlot + proofStatePolys0OpeningAtZSlot) %% Constants.R;
    s1BGb <- (proofCopyPermutationPolys1OpeningAtZSlot * stateBetaSlot + stateGammaSlot + proofStatePolys1OpeningAtZSlot) %% Constants.R;
    s2BGc <- (proofCopyPermutationPolys2OpeningAtZSlot * stateBetaSlot + stateGammaSlot + proofStatePolys2OpeningAtZSlot) %% Constants.R;
    s3G   <- (proofStatePolys3OpeningAtZSlot + stateGammaSlot) %% Constants.R;
    
    inv1 <- Constants.R - (statePowerOfAlpha4Slot * proofCopyPermutationGrandProductOpeningAtZOmegaSlot * s0BGa * s1BGb * s2BGc * s3G) %% Constants.R;
    inv2 <- Constants.R - (statePowerOfAlpha5Slot * stateL0AtZSlot) %% Constants.R;
    
    return (inv1 + inv2) %% Constants.R;
  }
}.

lemma permutationQuotientContribution_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_permutationQuotientContribution ~ PermutationQuotientContribution.low:
      ={arg, glob PermutationQuotientContribution} ==>
      ={res, glob PermutationQuotientContribution}
    ].
proof. proc.
  inline *; wp; skip; progress; by smt ().
qed.

section.

local module TMP = {
  proc low1(): uint256 = {
    var _res, _alpha4, _zperm_zOmega, _gamma, _beta, _factorMultiplier, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, _22, _l0AtZ, _alpha5, _26;
    _alpha4 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    _zperm_zOmega <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    _gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    _beta <@ Primops.mload(STATE_BETA_SLOT);
    _sigma0_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _a_z <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    _sigma1_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _b_z <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    _sigma2_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _c_z <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    _sigma3_z <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    _l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    _res <- (PurePrimops.mulmod _zperm_zOmega _alpha4 R_MOD);
    _factorMultiplier <- (PurePrimops.mulmod _sigma0_z _beta R_MOD);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma R_MOD);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _a_z R_MOD);
    _res <- (PurePrimops.mulmod _res _factorMultiplier R_MOD);
    _factorMultiplier <- (PurePrimops.mulmod _sigma1_z _beta R_MOD);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma R_MOD);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _b_z R_MOD);
    _res <- (PurePrimops.mulmod _res _factorMultiplier R_MOD);
    _factorMultiplier <- (PurePrimops.mulmod _sigma2_z _beta R_MOD);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma R_MOD);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _c_z R_MOD);
    _res <- (PurePrimops.mulmod _res _factorMultiplier R_MOD);
    _22 <- (PurePrimops.addmod _sigma3_z _gamma R_MOD);
    _res <- (PurePrimops.mulmod _res _22 R_MOD);
    _res <- (R_MOD - _res);
    _l0AtZ <- (PurePrimops.mulmod _l0AtZ _alpha5 R_MOD);
    _26 <- (R_MOD - _l0AtZ);
    _res <- (PurePrimops.addmod _res _26 R_MOD);
    return _res;
  }

  proc low2(): uint256 = {
    var _res, _alpha4, _zperm_zOmega, _gamma, _beta, _factorMultiplier, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, _l0AtZ, _alpha5, _26;
    var s0BGa, s1BGb, s2BGc, s3G;
    
    _alpha4 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    _zperm_zOmega <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    _gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    _beta <@ Primops.mload(STATE_BETA_SLOT);
    _sigma0_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _a_z <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    _sigma1_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _b_z <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    _sigma2_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _c_z <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    _sigma3_z <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    _l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    _res <- (PurePrimops.mulmod _zperm_zOmega _alpha4 R_MOD);
    
    s0BGa <- (PurePrimops.mulmod _sigma0_z _beta R_MOD);
    s0BGa <- (PurePrimops.addmod s0BGa _gamma R_MOD);
    s0BGa <- (PurePrimops.addmod s0BGa _a_z R_MOD);

    _factorMultiplier <- s0BGa;
    _res <- (PurePrimops.mulmod _res _factorMultiplier R_MOD);
    
    s1BGb <- (PurePrimops.mulmod _sigma1_z _beta R_MOD);
    s1BGb <- (PurePrimops.addmod s1BGb _gamma R_MOD);
    s1BGb <- (PurePrimops.addmod s1BGb _b_z R_MOD);

    _factorMultiplier <- s1BGb;
    _res <- (PurePrimops.mulmod _res _factorMultiplier R_MOD);

    s2BGc <- (PurePrimops.mulmod _sigma2_z _beta R_MOD);
    s2BGc <- (PurePrimops.addmod s2BGc _gamma R_MOD);
    s2BGc <- (PurePrimops.addmod s2BGc _c_z R_MOD);

    _factorMultiplier <- s2BGc;
    _res <- (PurePrimops.mulmod _res _factorMultiplier R_MOD);

    s3G   <- (PurePrimops.addmod _sigma3_z _gamma R_MOD);
    _res <- (PurePrimops.mulmod _res s3G R_MOD);
    
    _res <- (R_MOD - _res);
    _l0AtZ <- (PurePrimops.mulmod _l0AtZ _alpha5 R_MOD);
    _26 <- (R_MOD - _l0AtZ);
    _res <- (PurePrimops.addmod _res _26 R_MOD);
    return _res;
  }

  proc low3(): uint256 = {
    var _res1, _res2, _alpha4, _zperm_zOmega, _gamma, _beta, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, _l0AtZ, _alpha5;
    var s0BGa, s1BGb, s2BGc, s3G;
    var inv1, inv2;
    
    _alpha4 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    _zperm_zOmega <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    _gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    _beta <@ Primops.mload(STATE_BETA_SLOT);
    _sigma0_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _a_z <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    _sigma1_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _b_z <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    _sigma2_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _c_z <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    _sigma3_z <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    _l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    _res1 <- (PurePrimops.mulmod _zperm_zOmega _alpha4 R_MOD);
    
    s0BGa <- (PurePrimops.mulmod _sigma0_z _beta R_MOD);
    s0BGa <- (PurePrimops.addmod s0BGa _gamma R_MOD);
    s0BGa <- (PurePrimops.addmod s0BGa _a_z R_MOD);

    _res1 <- (PurePrimops.mulmod _res1 s0BGa R_MOD);
    
    s1BGb <- (PurePrimops.mulmod _sigma1_z _beta R_MOD);
    s1BGb <- (PurePrimops.addmod s1BGb _gamma R_MOD);
    s1BGb <- (PurePrimops.addmod s1BGb _b_z R_MOD);

    _res1 <- (PurePrimops.mulmod _res1 s1BGb R_MOD);

    s2BGc <- (PurePrimops.mulmod _sigma2_z _beta R_MOD);
    s2BGc <- (PurePrimops.addmod s2BGc _gamma R_MOD);
    s2BGc <- (PurePrimops.addmod s2BGc _c_z R_MOD);

    _res1 <- (PurePrimops.mulmod _res1 s2BGc R_MOD);

    s3G   <- (PurePrimops.addmod _sigma3_z _gamma R_MOD);
    _res1 <- (PurePrimops.mulmod _res1 s3G R_MOD);
    inv1 <- (R_MOD - _res1);
    
    _res2 <- (PurePrimops.mulmod _l0AtZ _alpha5 R_MOD);
    inv2 <- (R_MOD - _res2);

    return (PurePrimops.addmod inv1 inv2 R_MOD);
  }

  proc low4(): uint256 = {
    var _res1, _res2, _alpha4, _zperm_zOmega, _gamma, _beta, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, _l0AtZ, _alpha5;
    var s0BGa, s1BGb, s2BGc, s3G;
    var inv1, inv2;
    
    _alpha4 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    _zperm_zOmega <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    _gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    _beta <@ Primops.mload(STATE_BETA_SLOT);
    _sigma0_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _a_z <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    _sigma1_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _b_z <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    _sigma2_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _c_z <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    _sigma3_z <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    _l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    s0BGa <- (PurePrimops.mulmod _sigma0_z _beta R_MOD);
    s0BGa <- (PurePrimops.addmod s0BGa _gamma R_MOD);
    s0BGa <- (PurePrimops.addmod s0BGa _a_z R_MOD);
    
    s1BGb <- (PurePrimops.mulmod _sigma1_z _beta R_MOD);
    s1BGb <- (PurePrimops.addmod s1BGb _gamma R_MOD);
    s1BGb <- (PurePrimops.addmod s1BGb _b_z R_MOD);

    s2BGc <- (PurePrimops.mulmod _sigma2_z _beta R_MOD);
    s2BGc <- (PurePrimops.addmod s2BGc _gamma R_MOD);
    s2BGc <- (PurePrimops.addmod s2BGc _c_z R_MOD);

    s3G   <- (PurePrimops.addmod _sigma3_z _gamma R_MOD);

    _res1 <- (PurePrimops.mulmod _zperm_zOmega _alpha4 R_MOD);
    _res1 <- (PurePrimops.mulmod _res1 s0BGa R_MOD);
    _res1 <- (PurePrimops.mulmod _res1 s1BGb R_MOD);
    _res1 <- (PurePrimops.mulmod _res1 s2BGc R_MOD);
    _res1 <- (PurePrimops.mulmod _res1 s3G R_MOD);
    inv1 <- (R_MOD - _res1);
    
    _res2 <- (PurePrimops.mulmod _l0AtZ _alpha5 R_MOD);
    inv2 <- (R_MOD - _res2);

    return (PurePrimops.addmod inv1 inv2 R_MOD);
  }
}.


local lemma low_equiv_low1 :
equiv [PermutationQuotientContribution.low ~ TMP.low1 :
      ={arg, Primops.memory} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, Primops.memory} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
    ].
proof. proc.
  inline *; wp; skip; progress; smt ().
qed.

local lemma low1_equiv_low2 :
equiv [TMP.low1 ~ TMP.low2 :
      ={arg, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
    ].
proof. proc.
  inline *; wp; skip; progress; smt ().
qed.

local lemma low2_equiv_low3 :
equiv [TMP.low2 ~ TMP.low3 :
      ={arg, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
    ].
proof. proc.
  inline *; wp; skip; progress; smt ().
qed.

local lemma low3_equiv_low4 :
equiv [TMP.low3 ~ TMP.low4 :
      ={arg, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
    ].
proof. proc.
  inline *; wp; skip; progress; smt ().
qed.

local lemma low_equiv_low4 :
equiv [PermutationQuotientContribution.low ~ TMP.low4 :
      ={arg, Primops.memory} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, Primops.memory} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
    ].
proof.
transitivity TMP.low1
(={arg, Primops.memory} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, Primops.memory} /\
      !Primops.reverted{1} /\ !Primops.reverted{2})

(={arg, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}); progress.
exists Primops.memory{2} Primops.reverted{1}; progress. apply low_equiv_low1.
transitivity TMP.low2 (={arg, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}) (={arg, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}); progress.
exists Primops.memory{2} Primops.reverted{1}. progress. apply low1_equiv_low2.
transitivity TMP.low3 (={arg, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}) (={arg, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, glob TMP} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}); progress.
exists Primops.memory{2} Primops.reverted{1}. progress. apply low2_equiv_low3.
apply low3_equiv_low4.
qed.

import MemoryMap PurePrimops.
declare op m : mem.

lemma low_equiv_mid(
    statePowerOfAlpha4SlotG
    statePowerOfAlpha5SlotG
    proofCopyPermutationGrandProductOpeningAtZOmegaSlotG
    stateBetaSlotG
    stateGammaSlotG
    proofCopyPermutationPolys0OpeningAtZSlotG
    proofCopyPermutationPolys1OpeningAtZSlotG
    proofCopyPermutationPolys2OpeningAtZSlotG
    proofStatePolys0OpeningAtZSlotG
    proofStatePolys1OpeningAtZSlotG
    proofStatePolys2OpeningAtZSlotG
    proofStatePolys3OpeningAtZSlotG
    stateL0AtZSlotG : int
) :
equiv [PermutationQuotientContribution.low ~ PermutationQuotientContribution.mid :
  arg{2} = (
    statePowerOfAlpha4SlotG,
    statePowerOfAlpha5SlotG,
    proofCopyPermutationGrandProductOpeningAtZOmegaSlotG,
    stateBetaSlotG,
    stateGammaSlotG,
    proofCopyPermutationPolys0OpeningAtZSlotG,
    proofCopyPermutationPolys1OpeningAtZSlotG,
    proofCopyPermutationPolys2OpeningAtZSlotG,
    proofStatePolys0OpeningAtZSlotG,
    proofStatePolys1OpeningAtZSlotG,
    proofStatePolys2OpeningAtZSlotG,
    proofStatePolys3OpeningAtZSlotG,
    stateL0AtZSlotG) /\
  Primops.memory{1} = m /\
  !Primops.reverted{1} /\
  W256.to_uint (mload m STATE_POWER_OF_ALPHA_4_SLOT) = statePowerOfAlpha4SlotG /\
  W256.to_uint (mload m STATE_POWER_OF_ALPHA_5_SLOT) = statePowerOfAlpha5SlotG /\
  W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaSlotG /\
  W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaSlotG /\
  W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaSlotG /\
  W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZSlotG /\
  W256.to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZSlotG
  ==>
  !Primops.reverted{1} /\
  Primops.memory{1} = m /\
  res{2} = W256.to_uint res{1} /\
  0 <= res{2} < Constants.R
 ].
proof. 
transitivity
  TMP.low4
  ( ={arg, Primops.memory} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, Primops.memory} /\
      !Primops.reverted{1} /\ !Primops.reverted{2})
  (  arg{2} = (
    statePowerOfAlpha4SlotG,
    statePowerOfAlpha5SlotG,
    proofCopyPermutationGrandProductOpeningAtZOmegaSlotG,
    stateBetaSlotG,
    stateGammaSlotG,
    proofCopyPermutationPolys0OpeningAtZSlotG,
    proofCopyPermutationPolys1OpeningAtZSlotG,
    proofCopyPermutationPolys2OpeningAtZSlotG,
    proofStatePolys0OpeningAtZSlotG,
    proofStatePolys1OpeningAtZSlotG,
    proofStatePolys2OpeningAtZSlotG,
    proofStatePolys3OpeningAtZSlotG,
    stateL0AtZSlotG) /\
  Primops.memory{1} = m /\
  !Primops.reverted{1} /\
  W256.to_uint (mload m STATE_POWER_OF_ALPHA_4_SLOT) = statePowerOfAlpha4SlotG /\
  W256.to_uint (mload m STATE_POWER_OF_ALPHA_5_SLOT) = statePowerOfAlpha5SlotG /\
  W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaSlotG /\
  W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaSlotG /\
  W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaSlotG /\
  W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZSlotG /\
  W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZSlotG /\
  W256.to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZSlotG
  ==>
  !Primops.reverted{1} /\
  Primops.memory{1} = m /\
  res{2} = W256.to_uint res{1} /\
  0 <= res{2} < Constants.R).
progress. exists m Primops.reverted{1}. by auto.
by progress. by apply low_equiv_low4.

proc.

seq 13 0 : (#pre /\
  W256.to_uint _alpha4{1} = statePowerOfAlpha4Slot{2} /\
  W256.to_uint _alpha5{1} = statePowerOfAlpha5Slot{2} /\
  W256.to_uint _zperm_zOmega{1} = proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2} /\
  W256.to_uint _gamma{1} = stateGammaSlot{2} /\ 
  W256.to_uint _beta{1} = stateBetaSlot{2} /\
  W256.to_uint _sigma0_z{1} = proofCopyPermutationPolys0OpeningAtZSlot{2} /\
  W256.to_uint _sigma1_z{1} = proofCopyPermutationPolys1OpeningAtZSlot{2} /\
  W256.to_uint _sigma2_z{1} = proofCopyPermutationPolys2OpeningAtZSlot{2} /\
  W256.to_uint _sigma3_z{1} = proofStatePolys3OpeningAtZSlot{2} /\
  W256.to_uint _a_z{1} = proofStatePolys0OpeningAtZSlot{2} /\
  W256.to_uint _b_z{1} = proofStatePolys1OpeningAtZSlot{2} /\
  W256.to_uint _c_z{1} = proofStatePolys2OpeningAtZSlot{2} /\
  W256.to_uint _l0AtZ{1} = stateL0AtZSlotG).
call{1} (ConcretePrimops.mload_pspec m STATE_POWER_OF_ALPHA_5_SLOT).
call{1} (ConcretePrimops.mload_pspec m STATE_L_0_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec m STATE_BETA_SLOT).
call{1} (ConcretePrimops.mload_pspec m STATE_GAMMA_SLOT).
call{1} (ConcretePrimops.mload_pspec m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT).
call{1} (ConcretePrimops.mload_pspec m STATE_POWER_OF_ALPHA_4_SLOT).
skip; by progress.

seq 10 4 : (#pre /\ W256.to_uint s0BGa{1} = s0BGa{2} /\ W256.to_uint s1BGb{1} = s1BGb{2} /\ W256.to_uint s2BGc{1} = s2BGc{2} /\ W256.to_uint s2BGc{1} = s2BGc{2} /\ W256.to_uint s3G{1} = s3G{2}).
wp; skip; rewrite /addmod /mulmod; progress.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite H5 H4 H3 H9. smt.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite H6 H4 H3 H10. smt.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite H7 H4 H3 H11. smt.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite H7 H4 H3 H11. smt.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils).

seq 5 0 : (#pre /\ W256.to_uint _res1{1} = (statePowerOfAlpha4Slot{2} * proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2} * s0BGa{2} * s1BGb{2} * s2BGc{2} * s3G{2}) %% Constants.R).
wp; skip; rewrite /addmod /mulmod; progress.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite H2 H0. smt.

seq 1 1 : (#pre /\ W256.to_uint inv1{1} = inv1{2} /\ inv1{2} = (Constants.R - to_uint _res1{1})).
wp; skip; progress. rewrite -H13.
have ->:
 (Constants.R - to_uint _res1{1}) = (Constants.R - to_uint _res1{1}) %% W256.modulus.
 by smt().
rewrite -W256.of_uintK; by smt(@W256).
rewrite -H13. reflexivity.
 
seq 1 0 : (#pre /\ W256.to_uint _res2{1} = (statePowerOfAlpha5Slot{2} * stateL0AtZSlot{2}) %% Constants.R).
wp; skip; rewrite /addmod /mulmod; progress.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite H12 H1. smt.
 
seq 1 1 : (#pre /\ W256.to_uint inv2{1} = inv2{2} /\ inv2{2} = (Constants.R - to_uint _res2{1})).
wp; skip; progress. rewrite -H15.
have ->:
 (Constants.R - to_uint _res2{1}) = (Constants.R - to_uint _res2{1}) %% W256.modulus.
 by smt().
rewrite -W256.of_uintK; by smt(@W256).
rewrite -H15. reflexivity.

skip. progress. rewrite /addmod; progress. 
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils). smt. smt. smt.
qed. 

end section.
