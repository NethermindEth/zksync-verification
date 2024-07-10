pragma Goals:printall.

require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.
require import Utils.
require import VerifierConsts.
require import VerifierVars.
require import VerifierMem.

module PermutationQuotientContribution = {
  proc low(): uint256 = {
    var _res, tmp270, tmp271, _gamma, _beta, _factorMultiplier, tmp274, tmp275, tmp276, tmp277, tmp278, tmp279, tmp280, _22, usr_l0AtZ, tmp282, _26;
    tmp270 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    tmp271 <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    _res <- (PurePrimops.mulmod tmp271 tmp270 (W256.of_int Constants.R));
    _gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    _beta <@ Primops.mload(STATE_BETA_SLOT);
    tmp274 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.mulmod tmp274 _beta (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma (W256.of_int Constants.R));
    tmp275 <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier tmp275 (W256.of_int Constants.R));
    _res <- (PurePrimops.mulmod _res _factorMultiplier (W256.of_int Constants.R));
    tmp276 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.mulmod tmp276 _beta (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma (W256.of_int Constants.R));
    tmp277 <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier tmp277 (W256.of_int Constants.R));
    _res <- (PurePrimops.mulmod _res _factorMultiplier (W256.of_int Constants.R));
    tmp278 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.mulmod tmp278 _beta (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma (W256.of_int Constants.R));
    tmp279 <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier tmp279 (W256.of_int Constants.R));
    _res <- (PurePrimops.mulmod _res _factorMultiplier (W256.of_int Constants.R));
    tmp280 <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    _22 <- (PurePrimops.addmod tmp280 _gamma (W256.of_int Constants.R));
    _res <- (PurePrimops.mulmod _res _22 (W256.of_int Constants.R));
    _res <- ((W256.of_int Constants.R) - _res);
    usr_l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    tmp282 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    usr_l0AtZ <- (PurePrimops.mulmod usr_l0AtZ tmp282 (W256.of_int Constants.R));
    _26 <- ((W256.of_int Constants.R) - usr_l0AtZ);
    _res <- (PurePrimops.addmod _res _26 (W256.of_int Constants.R));
    return _res;
  }

  proc mid() : int = {
    var s0BGa, s1BGb, s2BGc, s3G, inv1, inv2;
    
    s0BGa <- (Sigma0_z * Beta + Gamma + A_z) %% Constants.R;
    s1BGb <- (Sigma1_z * Beta + Gamma + B_z) %% Constants.R;
    s2BGc <- (Sigma2_z * Beta + Gamma + C_z) %% Constants.R;
    s3G   <- (Sigma3_z + Gamma) %% Constants.R;

    inv1 <- Constants.R - (Alpha4 * Zperm_zOmega * s0BGa * s1BGb * s2BGc * s3G) %% Constants.R;
    inv2 <- Constants.R - (Alpha5 * L0_z) %% Constants.R;
    
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
    var _res, _alpha4, _zperm_zOmega, _gamma, _beta, _factorMultiplier, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, _22, usr_l0AtZ, _alpha5, _26;
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
    usr_l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    _res <- (PurePrimops.mulmod _zperm_zOmega _alpha4 (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.mulmod _sigma0_z _beta (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _a_z (W256.of_int Constants.R));
    _res <- (PurePrimops.mulmod _res _factorMultiplier (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.mulmod _sigma1_z _beta (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _b_z (W256.of_int Constants.R));
    _res <- (PurePrimops.mulmod _res _factorMultiplier (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.mulmod _sigma2_z _beta (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _gamma (W256.of_int Constants.R));
    _factorMultiplier <- (PurePrimops.addmod _factorMultiplier _c_z (W256.of_int Constants.R));
    _res <- (PurePrimops.mulmod _res _factorMultiplier (W256.of_int Constants.R));
    _22 <- (PurePrimops.addmod _sigma3_z _gamma (W256.of_int Constants.R));
    _res <- (PurePrimops.mulmod _res _22 (W256.of_int Constants.R));
    _res <- ((W256.of_int Constants.R) - _res);
    usr_l0AtZ <- (PurePrimops.mulmod usr_l0AtZ _alpha5 (W256.of_int Constants.R));
    _26 <- ((W256.of_int Constants.R) - usr_l0AtZ);
    _res <- (PurePrimops.addmod _res _26 (W256.of_int Constants.R));
    return _res;
  }

  proc low2(): uint256 = {
    var _res, _alpha4, _zperm_zOmega, _gamma, _beta, _factorMultiplier, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, usr_l0AtZ, _alpha5, _26;
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
    usr_l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    _res <- (PurePrimops.mulmod _zperm_zOmega _alpha4 (W256.of_int Constants.R));
    
    s0BGa <- (PurePrimops.mulmod _sigma0_z _beta (W256.of_int Constants.R));
    s0BGa <- (PurePrimops.addmod s0BGa _gamma (W256.of_int Constants.R));
    s0BGa <- (PurePrimops.addmod s0BGa _a_z (W256.of_int Constants.R));

    _factorMultiplier <- s0BGa;
    _res <- (PurePrimops.mulmod _res _factorMultiplier (W256.of_int Constants.R));
    
    s1BGb <- (PurePrimops.mulmod _sigma1_z _beta (W256.of_int Constants.R));
    s1BGb <- (PurePrimops.addmod s1BGb _gamma (W256.of_int Constants.R));
    s1BGb <- (PurePrimops.addmod s1BGb _b_z (W256.of_int Constants.R));

    _factorMultiplier <- s1BGb;
    _res <- (PurePrimops.mulmod _res _factorMultiplier (W256.of_int Constants.R));

    s2BGc <- (PurePrimops.mulmod _sigma2_z _beta (W256.of_int Constants.R));
    s2BGc <- (PurePrimops.addmod s2BGc _gamma (W256.of_int Constants.R));
    s2BGc <- (PurePrimops.addmod s2BGc _c_z (W256.of_int Constants.R));

    _factorMultiplier <- s2BGc;
    _res <- (PurePrimops.mulmod _res _factorMultiplier (W256.of_int Constants.R));

    s3G   <- (PurePrimops.addmod _sigma3_z _gamma (W256.of_int Constants.R));
    _res <- (PurePrimops.mulmod _res s3G (W256.of_int Constants.R));
    
    _res <- ((W256.of_int Constants.R) - _res);
    usr_l0AtZ <- (PurePrimops.mulmod usr_l0AtZ _alpha5 (W256.of_int Constants.R));
    _26 <- ((W256.of_int Constants.R) - usr_l0AtZ);
    _res <- (PurePrimops.addmod _res _26 (W256.of_int Constants.R));
    return _res;
  }

  proc low3(): uint256 = {
    var _res1, _res2, _alpha4, _zperm_zOmega, _gamma, _beta, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, usr_l0AtZ, _alpha5;
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
    usr_l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    _res1 <- (PurePrimops.mulmod _zperm_zOmega _alpha4 (W256.of_int Constants.R));
    
    s0BGa <- (PurePrimops.mulmod _sigma0_z _beta (W256.of_int Constants.R));
    s0BGa <- (PurePrimops.addmod s0BGa _gamma (W256.of_int Constants.R));
    s0BGa <- (PurePrimops.addmod s0BGa _a_z (W256.of_int Constants.R));

    _res1 <- (PurePrimops.mulmod _res1 s0BGa (W256.of_int Constants.R));
    
    s1BGb <- (PurePrimops.mulmod _sigma1_z _beta (W256.of_int Constants.R));
    s1BGb <- (PurePrimops.addmod s1BGb _gamma (W256.of_int Constants.R));
    s1BGb <- (PurePrimops.addmod s1BGb _b_z (W256.of_int Constants.R));

    _res1 <- (PurePrimops.mulmod _res1 s1BGb (W256.of_int Constants.R));

    s2BGc <- (PurePrimops.mulmod _sigma2_z _beta (W256.of_int Constants.R));
    s2BGc <- (PurePrimops.addmod s2BGc _gamma (W256.of_int Constants.R));
    s2BGc <- (PurePrimops.addmod s2BGc _c_z (W256.of_int Constants.R));

    _res1 <- (PurePrimops.mulmod _res1 s2BGc (W256.of_int Constants.R));

    s3G   <- (PurePrimops.addmod _sigma3_z _gamma (W256.of_int Constants.R));
    _res1 <- (PurePrimops.mulmod _res1 s3G (W256.of_int Constants.R));
    inv1 <- ((W256.of_int Constants.R) - _res1);
    
    _res2 <- (PurePrimops.mulmod usr_l0AtZ _alpha5 (W256.of_int Constants.R));
    inv2 <- ((W256.of_int Constants.R) - _res2);

    return (PurePrimops.addmod inv1 inv2 (W256.of_int Constants.R));
  }

  proc low4(): uint256 = {
    var _res1, _res2, _alpha4, _zperm_zOmega, _gamma, _beta, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, usr_l0AtZ, _alpha5;
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
    usr_l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    s0BGa <- (PurePrimops.mulmod _sigma0_z _beta (W256.of_int Constants.R));
    s0BGa <- (PurePrimops.addmod s0BGa _gamma (W256.of_int Constants.R));
    s0BGa <- (PurePrimops.addmod s0BGa _a_z (W256.of_int Constants.R));
    
    s1BGb <- (PurePrimops.mulmod _sigma1_z _beta (W256.of_int Constants.R));
    s1BGb <- (PurePrimops.addmod s1BGb _gamma (W256.of_int Constants.R));
    s1BGb <- (PurePrimops.addmod s1BGb _b_z (W256.of_int Constants.R));

    s2BGc <- (PurePrimops.mulmod _sigma2_z _beta (W256.of_int Constants.R));
    s2BGc <- (PurePrimops.addmod s2BGc _gamma (W256.of_int Constants.R));
    s2BGc <- (PurePrimops.addmod s2BGc _c_z (W256.of_int Constants.R));

    s3G   <- (PurePrimops.addmod _sigma3_z _gamma (W256.of_int Constants.R));

    _res1 <- (PurePrimops.mulmod _zperm_zOmega _alpha4 (W256.of_int Constants.R));
    _res1 <- (PurePrimops.mulmod _res1 s0BGa (W256.of_int Constants.R));
    _res1 <- (PurePrimops.mulmod _res1 s1BGb (W256.of_int Constants.R));
    _res1 <- (PurePrimops.mulmod _res1 s2BGc (W256.of_int Constants.R));
    _res1 <- (PurePrimops.mulmod _res1 s3G (W256.of_int Constants.R));
    inv1 <- ((W256.of_int Constants.R) - _res1);
    
    _res2 <- (PurePrimops.mulmod usr_l0AtZ _alpha5 (W256.of_int Constants.R));
    inv2 <- ((W256.of_int Constants.R) - _res2);

    return (PurePrimops.addmod inv1 inv2 (W256.of_int Constants.R));
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

import MemoryMap VerifierMem.
declare op m : mem.

pred permutationQuotientContribution_memory_vars = 
  alpha4_mem m /\
  alpha5_mem m /\
  beta_mem m /\
  gamma_mem m /\
  sigma0_z_mem m /\
  sigma1_z_mem m /\
  sigma2_z_mem m /\
  sigma3_z_mem m /\
  a_z_mem m /\
  b_z_mem m /\
  c_z_mem m /\  
  zperm_zOmega_mem m /\
  l0_z_mem m.

lemma low_equiv_mid :
equiv [PermutationQuotientContribution.low ~ PermutationQuotientContribution.mid :
   ={arg} /\
   Primops.memory{1} = m /\
   !Primops.reverted{1} /\ !Primops.reverted{2} /\
   permutationQuotientContribution_memory_vars
   ==>
   !Primops.reverted{1} /\ !Primops.reverted{2} /\
   Primops.memory{1} = m /\
   res{2} = W256.to_uint res{1}
 ].
proof. 
transitivity
  TMP.low4
  ( ={arg, Primops.memory} /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      ={res, Primops.memory} /\
      !Primops.reverted{1} /\ !Primops.reverted{2})
  (={arg} /\
   Primops.memory{1} = m /\
   !Primops.reverted{1} /\ !Primops.reverted{2} /\
   permutationQuotientContribution_memory_vars
   ==>
   !Primops.reverted{1} /\ !Primops.reverted{2} /\
   Primops.memory{1} = m /\
   res{2} = W256.to_uint res{1}).
progress; exists m Primops.reverted{1}; by auto.
by progress.
by apply low_equiv_low4.

rewrite /permutationQuotientContribution_memory_vars; proc.

seq 13 0 : (#pre /\
  W256.to_uint _alpha4{1} = Alpha4 /\
  W256.to_uint _alpha5{1} = Alpha5 /\
  W256.to_uint _zperm_zOmega{1} = Zperm_zOmega /\
  W256.to_uint _gamma{1} = Gamma /\ 
  W256.to_uint _beta{1} = Beta /\
  W256.to_uint _sigma0_z{1} = Sigma0_z /\
  W256.to_uint _sigma1_z{1} = Sigma1_z /\
  W256.to_uint _sigma2_z{1} = Sigma2_z /\
  W256.to_uint _sigma3_z{1} = Sigma3_z /\
  W256.to_uint _a_z{1} = A_z /\
  W256.to_uint _c_z{1} = C_z /\
  W256.to_uint _b_z{1} = B_z /\
  W256.to_uint usr_l0AtZ{1} = L0_z).
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
wp; skip; rewrite /addmod /mulmod; progress; rewrite !W256.of_uintK; by smt().

seq 5 0 : (#pre /\ W256.to_uint _res1{1} = (Alpha4 * Zperm_zOmega * s0BGa{2} * s1BGb{2} * s2BGc{2} * s3G{2}) %% Constants.R).
wp; skip; rewrite /addmod /mulmod; progress; rewrite !W256.of_uintK !R_mod_W256_R !mod_R_W256_mod_R; by smt().

seq 1 1 : (#pre /\ W256.to_uint inv1{1} = inv1{2}).
wp; skip; progress; rewrite -H27.
have ->:
 (Constants.R - to_uint _res1{1}) = (Constants.R - to_uint _res1{1}) %% W256.modulus.
 by smt().
rewrite -W256.of_uintK; by smt(@W256).

seq 1 0 : (#pre /\ W256.to_uint _res2{1} = (Alpha5 * L0_z) %% Constants.R).
wp; skip; rewrite /addmod /mulmod; progress; rewrite !W256.of_uintK !R_mod_W256_R !mod_R_W256_mod_R; by smt().

seq 1 1 : (#pre /\ W256.to_uint inv2{1} = inv2{2}).
wp; skip; progress; rewrite -H28.
have ->:
 (Constants.R - to_uint _res2{1}) = (Constants.R - to_uint _res2{1}) %% W256.modulus.
 by smt().
rewrite -W256.of_uintK; by smt(@W256).

skip; rewrite /addmod; progress; rewrite !W256.of_uintK !R_mod_W256_R !mod_R_W256_mod_R; 
by reflexivity.

qed. 

end section.

