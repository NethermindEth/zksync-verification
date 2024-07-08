pragma Goals:printall.

require import AllCore Int IntDiv.
require import Constants Field Verifier UInt256 YulPrimops PurePrimops VerifierConsts.

module PermutationQuotientContribution = {

  proc low(): uint256 = {
    var usr_res, a4, zperm_zo, usr_gamma, usr_beta, usr_factorMultiplier, sigma0_z, a_z, sigma1_z, b_z, sigma2_z, c_z, sigma3_z, _22, l0AtZ, a5, _26;
    a4 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    zperm_zo <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    usr_res <- (PurePrimops.mulmod a4 zperm_zo (W256.of_int R));
    
    usr_gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    usr_beta <@ Primops.mload(STATE_BETA_SLOT);
    
    sigma0_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.mulmod sigma0_z usr_beta (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int R));
    a_z <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier a_z (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));
    
    sigma1_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.mulmod sigma1_z usr_beta (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int R));
    b_z <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier b_z (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));
    
    sigma2_z <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.mulmod sigma2_z usr_beta (W256.of_int R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int R));
    c_z <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier c_z (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int R));
    
    sigma3_z <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    _22 <- (PurePrimops.addmod sigma3_z usr_gamma (W256.of_int R));
    usr_res <- (PurePrimops.mulmod usr_res _22 (W256.of_int R));
    usr_res <- ((W256.of_int R) - usr_res);
    
    l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    a5 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    l0AtZ <- (PurePrimops.mulmod l0AtZ a5 (W256.of_int R));
    _26 <- ((W256.of_int R) - l0AtZ);
    usr_res <- (PurePrimops.addmod usr_res _26 (W256.of_int R));

    return usr_res;
  }

  (* var a4, a5, b, g : Fr *)
  (* var zp_z0, l0_z : Fr *)
  (* var s0_z, s1_z, s2_z, s3_z : Fr *)
  (* var a_z, b_z, c_z : Fr *)
 
  (* proc high() : Fr = { *)
  (*   var s0BGa, s1BGb, s2BGc, s3G : Fr; *)

  (*   s0BGa <- s0_z * b + g + a_z; *)
  (*   s1BGb <- s1_z * b + g + b_z; *)
  (*   s2BGc <- s2_z * b + g + c_z; *)
  (*   s3G   <- s3_z + g; *)
    
  (*   return (-(a4 * zp_z0 * s0BGa * s1BGb * s2BGc * s3G)) - (a5 * l0_z); *)
  (* } *)
 
  (* var _a4, _a5, _b, _g : int *)
  (* var _zp_z0, _l0_z : int *)
  (* var _s0_z, _s1_z, _s2_z, _s3_z : int *)
  (* var _a_z, _b_z, _c_z : int *)
  
  (* proc mid() : int = { *)
  (*   var s0BGa, s1BGb, s2BGc, s3G : int; *)

  (*   s0BGa <- (_s0_z * _b + _g + _a_z)%%R; *)
  (*   s1BGb <- (_s1_z * _b + _g + _b_z)%%R; *)
  (*   s2BGc <- (_s2_z * _b + _g + _c_z)%%R; *)
  (*   s3G   <- (_s3_z + _g)%%R; *)

  (*   return ((R - (_a4 * _zp_z0 * s0BGa * s1BGb * s2BGc * s3G)) + (R - (_a5 * _l0_z)))%%R; *)
  (* }   *)
}.

lemma permutationQuotientContribution_extracted_equiv_low :
equiv [Verifier.usr_permutationQuotientContribution ~ PermutationQuotientContribution.low :
      ={arg, glob PermutationQuotientContribution} ==> ={res, glob PermutationQuotientContribution}].
proof. proc.
inline *; wp; skip; progress; smt ().
qed.


(* op permutationQuotientContribution_Mspec *)
(*   (A4 A5 zperm_zO L0_z *)
(*    sigma0_z sigma1_z sigma2_z sigma3_z *)
(*    G B *)
(*    a_z b_z c_z *)
(*    rs : int) : bool = *)
(*   let s0BGa = (sigma0_z * B + G + a_z)%%r in let s1BGb = (sigma1_z * B + G + b_z)%%r in *)
(*   let s2BGc = (sigma2_z * B + G + c_z)%%r in let s3G   = (sigma3_z + G)%%r in *)
(*   rs = ((r - (A4 * zperm_zO * s0BGa * s1BGb * s2BGc * s3G))%%r + (r - (A5 * L0_z)))%%r. *)

(* op permutationQuotientContribution_Hspec *)
(*   (A zperm_zO L0_z *)
(*    sigma0_z sigma1_z sigma2_z sigma3_z *)
(*    G B *)
(*    a_z b_z c_z *)
(*    rs : Fr) : bool = *)
(*   let s0BGa = sigma0_z * B + G + a_z in let s1BGb = sigma1_z * B + G + b_z in *)
(*   let s2BGc = sigma2_z * B + G + c_z in let s3G   = sigma3_z + G in *)
(*   rs = (-(A^4 * zperm_zO * s0BGa * s1BGb * s2BGc * s3G)) - (A^5 * L0_z). *)
