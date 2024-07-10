pragma Goals:printall.

require import AllCore Int IntDiv.
require import Constants Field Verifier Memory UInt256 YulPrimops PurePrimops VerifierConsts.

theory PermutationQuotientContribution.

import MemoryMap.

op memory : mem.
pred in_mem (c : uint256) (v : int) = W256.to_uint (PurePrimops.mload memory c) = v.

op Alpha4 : int.
op Alpha5 : int. 
op Gamma : int. 
op Beta  : int.
op sigma0_z : int. 
op sigma1_z : int. 
op sigma2_z : int. 
op sigma3_z : int. 
op a_z : int. 
op b_z : int. 
op c_z : int. 
op zperm_zO : int. 
op l0_z : int. 

axiom alpha4_mem : in_mem STATE_POWER_OF_ALPHA_4_SLOT Alpha4.
axiom alpha5_mem : in_mem STATE_POWER_OF_ALPHA_5_SLOT Alpha5.
axiom gamma_mem : in_mem STATE_GAMMA_SLOT Gamma.
axiom beta_mem  : in_mem STATE_BETA_SLOT Beta.
axiom sigma0_z_mem : in_mem PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT sigma0_z.
axiom sigma1_z_mem : in_mem PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT sigma1_z.
axiom sigma2_z_mem : in_mem PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT sigma2_z.
axiom sigma3_z_mem : in_mem PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT sigma3_z.
axiom a_z_mem : in_mem PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT a_z.
axiom b_z_mem : in_mem PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT b_z.
axiom c_z_mem : in_mem PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT c_z.
axiom zperm_zO_mem : in_mem PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT zperm_zO.
axiom l0_z_mem : in_mem STATE_L_0_AT_Z_SLOT l0_z.

module M = {

  proc low(): uint256 = {
    var usr_res, tmp270, tmp271, usr_gamma, usr_beta, usr_factorMultiplier, tmp274, tmp275, tmp276, tmp277, tmp278, tmp279, tmp280, _22, usr_l0AtZ, tmp282, _26;
    tmp270 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    tmp271 <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    usr_res <- (PurePrimops.mulmod tmp271 tmp270 (W256.of_int R));
    usr_gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    usr_beta <@ Primops.mload(STATE_BETA_SLOT);
    tmp274 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.mulmod tmp274 usr_beta (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int R));
    tmp275 <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier tmp275 (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));
    tmp276 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.mulmod tmp276 usr_beta (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int R));
    tmp277 <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier tmp277 (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));
    tmp278 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.mulmod tmp278 usr_beta (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int R));
    tmp279 <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier tmp279 (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));
    tmp280 <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    _22 <- (PurePrimops.addmod tmp280 usr_gamma (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res _22 (W256.of_int R));
    usr_res <- ((W256.of_int R) - usr_res);
    usr_l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    tmp282 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    usr_l0AtZ <- (PurePrimops.mulmod usr_l0AtZ tmp282 (W256.of_int R));
    _26 <- ((W256.of_int R) - usr_l0AtZ);
    usr_res <- (PurePrimops.addmod usr_res _26 (W256.of_int R));
    return usr_res;
  }
    
  proc mid() : int = {
    var s0BGa, s1BGb, s2BGc, s3G, inv1, inv2;
    
    s0BGa <- (sigma0_z * Beta + Gamma + a_z)%%R;
    s1BGb <- (sigma1_z * Beta + Gamma + b_z)%%R;
    s2BGc <- (sigma2_z * Beta + Gamma + c_z)%%R;
    s3G   <- (sigma3_z + Gamma)%%R;

    inv1 <- R - (Alpha4 * zperm_zO * s0BGa * s1BGb * s2BGc * s3G)%%R;
    inv2 <- R - (Alpha5 * l0_z)%%R;
    
    return (inv1 + inv2)%%R;
  }
}.

lemma extracted_equiv_low :
     equiv [Verifier.usr_permutationQuotientContribution ~ M.low :
           ={arg, glob M} ==> ={res, glob M}].
proof. proc.
  inline *; wp; skip; progress; smt ().
qed.

section T.

local module TMP = {
  proc low1(): uint256 = {
    var usr_res, _alpha4, _zperm_zOmega, usr_gamma, usr_beta, usr_factorMultiplier, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, _22, usr_l0AtZ, _alpha5, _26;
    _alpha4 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    _zperm_zOmega <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    usr_gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    usr_beta <@ Primops.mload(STATE_BETA_SLOT);
    _sigma0_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _a_z <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    _sigma1_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _b_z <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    _sigma2_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _c_z <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    _sigma3_z <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    usr_l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    usr_res <- (PurePrimops.mulmod _zperm_zOmega _alpha4 (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.mulmod _sigma0_z usr_beta (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier _a_z (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.mulmod _sigma1_z usr_beta (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier _b_z (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.mulmod _sigma2_z usr_beta (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier _c_z (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));
    _22 <- (PurePrimops.addmod _sigma3_z usr_gamma (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res _22 (W256.of_int R));
    usr_res <- ((W256.of_int R) - usr_res);
    usr_l0AtZ <- (PurePrimops.mulmod usr_l0AtZ _alpha5 (W256.of_int R));
    _26 <- ((W256.of_int R) - usr_l0AtZ);
    usr_res <- (PurePrimops.addmod usr_res _26 (W256.of_int R));
    return usr_res;
  }

  proc low2(): uint256 = {
    var usr_res, _alpha4, _zperm_zOmega, usr_gamma, usr_beta, usr_factorMultiplier, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, usr_l0AtZ, _alpha5, _26;
    var s0BGa, s1BGb, s2BGc, s3G;
    
    _alpha4 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    _zperm_zOmega <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    usr_gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    usr_beta <@ Primops.mload(STATE_BETA_SLOT);
    _sigma0_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _a_z <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    _sigma1_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _b_z <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    _sigma2_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _c_z <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    _sigma3_z <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    usr_l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    usr_res <- (PurePrimops.mulmod _zperm_zOmega _alpha4 (W256.of_int R));
    
    s0BGa <- (PurePrimops.mulmod _sigma0_z usr_beta (W256.of_int R));
    s0BGa <- (PurePrimops.addmod s0BGa usr_gamma (W256.of_int R));
    s0BGa <- (PurePrimops.addmod s0BGa _a_z (W256.of_int R));

    usr_factorMultiplier <- s0BGa;
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));
    
    s1BGb <- (PurePrimops.mulmod _sigma1_z usr_beta (W256.of_int R));
    s1BGb <- (PurePrimops.addmod s1BGb usr_gamma (W256.of_int R));
    s1BGb <- (PurePrimops.addmod s1BGb _b_z (W256.of_int R));

    usr_factorMultiplier <- s1BGb;
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));

    s2BGc <- (PurePrimops.mulmod _sigma2_z usr_beta (W256.of_int R));
    s2BGc <- (PurePrimops.addmod s2BGc usr_gamma (W256.of_int R));
    s2BGc <- (PurePrimops.addmod s2BGc _c_z (W256.of_int R));

    usr_factorMultiplier <- s2BGc;
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));

    s3G   <- (PurePrimops.addmod _sigma3_z usr_gamma (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res s3G (W256.of_int R));
    
    usr_res <- ((W256.of_int R) - usr_res);
    usr_l0AtZ <- (PurePrimops.mulmod usr_l0AtZ _alpha5 (W256.of_int R));
    _26 <- ((W256.of_int R) - usr_l0AtZ);
    usr_res <- (PurePrimops.addmod usr_res _26 (W256.of_int R));
    return usr_res;
  }

  proc low3(): uint256 = {
    var usr_res1, usr_res2, _alpha4, _zperm_zOmega, usr_gamma, usr_beta, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, usr_l0AtZ, _alpha5;
    var s0BGa, s1BGb, s2BGc, s3G;
    var inv1, inv2;
    
    _alpha4 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    _zperm_zOmega <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    usr_gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    usr_beta <@ Primops.mload(STATE_BETA_SLOT);
    _sigma0_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _a_z <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    _sigma1_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _b_z <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    _sigma2_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _c_z <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    _sigma3_z <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    usr_l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    usr_res1 <- (PurePrimops.mulmod _zperm_zOmega _alpha4 (W256.of_int R));
    
    s0BGa <- (PurePrimops.mulmod _sigma0_z usr_beta (W256.of_int R));
    s0BGa <- (PurePrimops.addmod s0BGa usr_gamma (W256.of_int R));
    s0BGa <- (PurePrimops.addmod s0BGa _a_z (W256.of_int R));

    usr_res1 <- (PurePrimops.mulmod usr_res1 s0BGa (W256.of_int R));
    
    s1BGb <- (PurePrimops.mulmod _sigma1_z usr_beta (W256.of_int R));
    s1BGb <- (PurePrimops.addmod s1BGb usr_gamma (W256.of_int R));
    s1BGb <- (PurePrimops.addmod s1BGb _b_z (W256.of_int R));

    usr_res1 <- (PurePrimops.mulmod usr_res1 s1BGb (W256.of_int R));

    s2BGc <- (PurePrimops.mulmod _sigma2_z usr_beta (W256.of_int R));
    s2BGc <- (PurePrimops.addmod s2BGc usr_gamma (W256.of_int R));
    s2BGc <- (PurePrimops.addmod s2BGc _c_z (W256.of_int R));

    usr_res1 <- (PurePrimops.mulmod usr_res1 s2BGc (W256.of_int R));

    s3G   <- (PurePrimops.addmod _sigma3_z usr_gamma (W256.of_int R));
    usr_res1 <- (PurePrimops.mulmod usr_res1 s3G (W256.of_int R));
    inv1 <- ((W256.of_int R) - usr_res1);
    
    usr_res2 <- (PurePrimops.mulmod usr_l0AtZ _alpha5 (W256.of_int R));
    inv2 <- ((W256.of_int R) - usr_res2);

    return (PurePrimops.addmod inv1 inv2 (W256.of_int R));
  }

  proc low4(): uint256 = {
    var usr_res1, usr_res2, _alpha4, _zperm_zOmega, usr_gamma, usr_beta, _sigma0_z, _a_z, _sigma1_z, _b_z, _sigma2_z, _c_z, _sigma3_z, usr_l0AtZ, _alpha5;
    var s0BGa, s1BGb, s2BGc, s3G;
    var inv1, inv2;
    
    _alpha4 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    _zperm_zOmega <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    usr_gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    usr_beta <@ Primops.mload(STATE_BETA_SLOT);
    _sigma0_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _a_z <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    _sigma1_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _b_z <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    _sigma2_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _c_z <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    _sigma3_z <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    usr_l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _alpha5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    
    s0BGa <- (PurePrimops.mulmod _sigma0_z usr_beta (W256.of_int R));
    s0BGa <- (PurePrimops.addmod s0BGa usr_gamma (W256.of_int R));
    s0BGa <- (PurePrimops.addmod s0BGa _a_z (W256.of_int R));
    
    s1BGb <- (PurePrimops.mulmod _sigma1_z usr_beta (W256.of_int R));
    s1BGb <- (PurePrimops.addmod s1BGb usr_gamma (W256.of_int R));
    s1BGb <- (PurePrimops.addmod s1BGb _b_z (W256.of_int R));

    s2BGc <- (PurePrimops.mulmod _sigma2_z usr_beta (W256.of_int R));
    s2BGc <- (PurePrimops.addmod s2BGc usr_gamma (W256.of_int R));
    s2BGc <- (PurePrimops.addmod s2BGc _c_z (W256.of_int R));

    s3G   <- (PurePrimops.addmod _sigma3_z usr_gamma (W256.of_int R));

    usr_res1 <- (PurePrimops.mulmod _zperm_zOmega _alpha4 (W256.of_int R));
    usr_res1 <- (PurePrimops.mulmod usr_res1 s0BGa (W256.of_int R));
    usr_res1 <- (PurePrimops.mulmod usr_res1 s1BGb (W256.of_int R));
    usr_res1 <- (PurePrimops.mulmod usr_res1 s2BGc (W256.of_int R));
    usr_res1 <- (PurePrimops.mulmod usr_res1 s3G (W256.of_int R));
    inv1 <- ((W256.of_int R) - usr_res1);
    
    usr_res2 <- (PurePrimops.mulmod usr_l0AtZ _alpha5 (W256.of_int R));
    inv2 <- ((W256.of_int R) - usr_res2);

    return (PurePrimops.addmod inv1 inv2 (W256.of_int R));
  }
}.

local lemma low_equiv_low1 :
     equiv [M.low ~ TMP.low1 : ={arg, Primops.memory} ==> ={res, Primops.memory}].
proof. proc.
  inline *; wp; skip; progress; smt ().
qed.

local lemma low1_equiv_low2 :
     equiv [TMP.low1 ~ TMP.low2 : ={arg, glob TMP} ==> ={res, glob TMP}].
proof. proc.
  inline *; wp; skip; progress; smt ().
qed.

local lemma low2_equiv_low3 :
     equiv [TMP.low2 ~ TMP.low3 : ={arg, glob TMP} ==> ={res, glob TMP}].
proof. proc.
  inline *; wp; skip; progress; smt ().
qed.

local lemma low3_equiv_low4 :
     equiv [TMP.low3 ~ TMP.low4 : ={arg, glob TMP} ==> ={res, glob TMP}].
proof. proc.
  inline *; wp; skip; progress; smt ().
qed.

local lemma low_equiv_low4 :
     equiv [M.low ~ TMP.low4 : ={arg, Primops.memory} ==> ={res, Primops.memory}].
proof.
transitivity TMP.low1 (={arg, glob M} ==> ={res, glob M}) (={arg, Primops.memory} ==> ={res, Primops.memory}); progress.
exists Primops.memory{2}. progress. apply low_equiv_low1.
transitivity TMP.low2 (={arg, glob TMP} ==> ={res, glob TMP}) (={arg, glob TMP} ==> ={res, glob TMP}); progress.
exists Primops.memory{2}. progress. apply low1_equiv_low2.
transitivity TMP.low3 (={arg, glob TMP} ==> ={res, glob TMP}) (={arg, glob TMP} ==> ={res, glob TMP}); progress.
exists Primops.memory{2}. progress. apply low2_equiv_low3.
apply low3_equiv_low4.
qed.

lemma aux1 (n : int) : n %% R %% W256.modulus = n %% R. by smt(). qed.
lemma aux2 : R %% W256.modulus = R. by smt(). qed.

lemma low_equiv_mid :
equiv [M.low ~ M.mid :
   ={arg, glob M} /\
   Primops.memory{1} = memory /\
   !Primops.reverted{1} /\
   !Primops.reverted{2}
   ==>
   W256.to_uint res{1} = res{2}
 ].
proof. 
transitivity TMP.low4 (={arg, glob M} ==> ={res, glob M}) (={arg} /\ Primops.memory{1} = memory /\
   !Primops.reverted{1} /\
   !Primops.reverted{2} ==> to_uint res{1} = res{2}); progress.
exists memory Primops.reverted{1}. auto. apply low_equiv_low4.
proc.
seq 13 0 : (#pre /\
  W256.to_uint _alpha4{1} = Alpha4 /\
  W256.to_uint _alpha5{1} = Alpha5 /\
  W256.to_uint _zperm_zOmega{1} = zperm_zO /\
  W256.to_uint usr_gamma{1} = Gamma /\ 
  W256.to_uint usr_beta{1} = Beta /\
  W256.to_uint _sigma0_z{1} = sigma0_z /\
  W256.to_uint _sigma1_z{1} = sigma1_z /\
  W256.to_uint _sigma2_z{1} = sigma2_z /\
  W256.to_uint _sigma3_z{1} = sigma3_z /\
  W256.to_uint _a_z{1} = a_z /\
  W256.to_uint _c_z{1} = c_z /\
  W256.to_uint _b_z{1} = b_z /\
  W256.to_uint usr_l0AtZ{1} = l0_z).
call{1} (ConcretePrimops.mload_pspec memory STATE_POWER_OF_ALPHA_5_SLOT).
call{1} (ConcretePrimops.mload_pspec memory STATE_L_0_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec memory PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec memory PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec memory PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec memory PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec memory PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec memory PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec memory PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec memory STATE_BETA_SLOT).
call{1} (ConcretePrimops.mload_pspec memory STATE_GAMMA_SLOT).
call{1} (ConcretePrimops.mload_pspec memory PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT).
call{1} (ConcretePrimops.mload_pspec memory STATE_POWER_OF_ALPHA_4_SLOT).
skip; progress. 
apply alpha4_mem. apply alpha5_mem. apply zperm_zO_mem. apply gamma_mem. apply beta_mem. apply sigma0_z_mem. apply sigma1_z_mem. apply sigma2_z_mem. apply sigma3_z_mem. apply a_z_mem. apply c_z_mem. apply b_z_mem. apply l0_z_mem.

seq 10 4 : (#pre /\ W256.to_uint s0BGa{1} = s0BGa{2} /\ W256.to_uint s1BGb{1} = s1BGb{2} /\ W256.to_uint s2BGc{1} = s2BGc{2} /\ W256.to_uint s2BGc{1} = s2BGc{2} /\ W256.to_uint s3G{1} = s3G{2}). wp; skip; rewrite /addmod /mulmod; progress; rewrite !W256.of_uintK; by smt().

seq 5 0 : (#pre /\ W256.to_uint usr_res1{1} = (Alpha4 * zperm_zO * s0BGa{2} * s1BGb{2} * s2BGc{2} * s3G{2})%%R). wp; skip; rewrite /addmod /mulmod; progress; rewrite !W256.of_uintK !aux2 !aux1; by smt().

seq 1 1 : (#pre /\ W256.to_uint inv1{1} = inv1{2}).
wp. skip. progress. rewrite -H14.
have T: (R - to_uint usr_res1{1}) = (R - to_uint usr_res1{1}) %% W256.modulus. by smt().
rewrite T -W256.of_uintK. smt(@W256).

seq 1 0 : (#pre /\ W256.to_uint usr_res2{1} = (Alpha5 * l0_z)%%R). wp; skip; rewrite /addmod /mulmod; progress; rewrite !W256.of_uintK !aux2 !aux1; by smt().

seq 1 1 : (#pre /\ W256.to_uint inv2{1} = inv2{2}).
wp. skip. progress. rewrite -H15.
have T: (R - to_uint usr_res2{1}) = (R - to_uint usr_res2{1}) %% W256.modulus. by smt().
rewrite T -W256.of_uintK. smt(@W256).

skip. progress. rewrite /addmod. progress. rewrite !W256.of_uintK !aux2 !aux1. by smt().
qed. 

end section T.

end PermutationQuotientContribution.

clone PermutationQuotientContribution as PQC.

print PQC.alpha4_mem.

with
  op Alpha4 <- 1
proof *.
realize alpha4_mem.

   
print PQC.low_equiv_mid.
