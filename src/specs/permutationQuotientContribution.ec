pragma Goals:printall.

require import AllCore Int IntDiv Constants Field.

module PermutationQuotientContribution = {
  var a4, a5, b, g : Fr
  var zp_z0, l0_z : Fr
  var s0_z, s1_z, s2_z, s3_z : Fr
  var a_z, b_z, c_z : Fr
 
  proc high() : Fr = {
    var s0BGa, s1BGb, s2BGc, s3G : Fr;

    s0BGa <- s0_z * b + g + a_z;
    s1BGb <- s1_z * b + g + b_z;
    s2BGc <- s2_z * b + g + c_z;
    s3G   <- s3_z + g;
    
    return (-(a4 * zp_z0 * s0BGa * s1BGb * s2BGc * s3G)) - (a5 * l0_z);
  }
 
  var _a4, _a5, _b, _g : int
  var _zp_z0, _l0_z : int
  var _s0_z, _s1_z, _s2_z, _s3_z : int
  var _a_z, _b_z, _c_z : int
  
  proc mid() : int = {
    var s0BGa, s1BGb, s2BGc, s3G : int;

    s0BGa <- (_s0_z * _b + _g + _a_z)%%R;
    s1BGb <- (_s1_z * _b + _g + _b_z)%%R;
    s2BGc <- (_s2_z * _b + _g + _c_z)%%R;
    s3G   <- (_s3_z + _g)%%R;

    return ((R - (_a4 * _zp_z0 * s0BGa * s1BGb * s2BGc * s3G)) + (R - (_a5 * _l0_z)))%%R;
  }  
}.

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
