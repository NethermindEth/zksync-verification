pragma Goals:printall.

require import AllCore Int IntDiv Wheels Constants Field.

op permutationQuotientContribution_Mspec
  (A4 A5 zperm_zO L0_z
   sigma0_z sigma1_z sigma2_z sigma3_z
   G B
   a_z b_z c_z
   rs : int) : bool =
  let s0BGa = (sigma0_z * B + G + a_z)%%r in let s1BGb = (sigma1_z * B + G + b_z)%%r in
  let s2BGc = (sigma2_z * B + G + c_z)%%r in let s3G   = (sigma3_z + G)%%r in
  rs = ((r - (A4 * zperm_zO * s0BGa * s1BGb * s2BGc * s3G)%%r) + (r - (A5 * L0_z)%%r))%%r.

op permutationQuotientContribution_Hspec
  (A4 A5 zperm_zO L0_z
   sigma0_z sigma1_z sigma2_z sigma3_z
   G B
   a_z b_z c_z
   rs : Fr) : bool =
  let s0BGa = sigma0_z * B + G + a_z in let s1BGb = sigma1_z * B + G + b_z in
  let s2BGc = sigma2_z * B + G + c_z in let s3G   = sigma3_z + G in
  rs = (-(A4 * zperm_zO * s0BGa * s1BGb * s2BGc * s3G)) - (A5 * L0_z).
