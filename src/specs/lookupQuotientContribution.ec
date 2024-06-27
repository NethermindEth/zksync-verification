pragma Goals:printall.

require import AllCore Int IntDiv Constants Field.

module LookupQuotientContribution = {
  var a6, a7, a8, b', g' : Fr
  var l0_z, ln1_z : Fr
  var s_z0, zl_z0 : Fr
  var z : Fr
  
  proc high() : Fr = {
    var a6_c, a7_c, a8_c : Fr;

    a6_c <- a6 * (s_z0 * b' + g' * (b' + one)) * ((z - OMEGAFr^(DOMAIN_SIZE - 1)) * zl_z0);
    a7_c <- a7 * l0_z;
    a8_c <- a8 * ln1_z * (g' * (b' + one))^(DOMAIN_SIZE - 1);
    
    return a6 - a7 - a8;
  }
}.

(* op lookupQuotientContributionn_Mspec *)
(*   (A4 A5 zperm_zO L0_z *)
(*    sigma0_z sigma1_z sigma2_z sigma3_z *)
(*    G B *)
(*    a_z b_z c_z *)
(*    rs : int) : bool = *)
(*   let s0BGa = (sigma0_z * B + G + a_z)%%r in let s1BGb = (sigma1_z * B + G + b_z)%%r in *)
(*   let s2BGc = (sigma2_z * B + G + c_z)%%r in let s3G   = (sigma3_z + G)%%r in *)
(*   rs = ((r - (A4 * zperm_zO * s0BGa * s1BGb * s2BGc * s3G))%%r + (r - (A5 * L0_z)))%%r. *)

(* op lookupQuotientContribution_Mspec *)
(*   (A6 A7 A8 L0_z Ln1_z Bl Gl s_zO zl_zO z rs : int) *)

(* op lookupQuotientContribution_Hspec *)
(*   (A6 A7 A8 L0_z Ln1_z Bl Gl s_zO zl_zO z rs : Fr) : bool =  *)
(*   let a6 = (A6 * (s_zO * Bl + Gl * (Bl + one)) * (z - omegaFr^(domain_size - 1)) * zl_zO) in *)
(*   let a7 = (A7 * L0_z) in let a8 = (A8 * Ln1_z * (Gl * (Bl + one))^(domain_size - 1)) in *)
(*   rs = a6 - a7 - a8. *)
