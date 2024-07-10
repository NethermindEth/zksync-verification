require        Constants.
require import PointAddAssign.
require import PointMulAndAddIntoDest.
require import PointMulIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module MainGateLinearisationContributionWithV = {
  proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256, stateOpening3AtZ : uint256): unit = {
  var _6, _8, _12, _15, _17, coeff;
    PointMulIntoDest.low(W256.of_int 512, stateOpening0AtZ, dest);
    PointMulAndAddIntoDest.low(W256.of_int 576, stateOpening1AtZ, dest);
    PointMulAndAddIntoDest.low(W256.of_int 640, stateOpening2AtZ, dest);
    PointMulAndAddIntoDest.low(W256.of_int 704, stateOpening3AtZ, dest);
    _6 <- (PurePrimops.mulmod stateOpening0AtZ stateOpening1AtZ (W256.of_int Constants.R));
    PointMulAndAddIntoDest.low(W256.of_int 768, _6, dest);
    _8 <- (PurePrimops.mulmod stateOpening0AtZ stateOpening2AtZ (W256.of_int Constants.R));
    PointMulAndAddIntoDest.low(W256.of_int 832, _8, dest);
    PointAddAssign.low(dest, W256.of_int 896);
    _12 <@ Primops.mload(W256.of_int 2688);
    PointMulAndAddIntoDest.low(W256.of_int 960, _12, dest);
    _15 <@ Primops.mload(W256.of_int 4000);
    _17 <@ Primops.mload(W256.of_int 2720);
    coeff <- (PurePrimops.mulmod _17 _15 (W256.of_int Constants.R));
    PointMulIntoDest.low(dest, coeff, dest);
  }
}.

lemma mainGateLinearisationContributionWithV_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_mainGateLinearisationContributionWithV ~ MainGateLinearisationContributionWithV.low :
      ={arg, glob MainGateLinearisationContributionWithV} ==>
      ={res, glob MainGateLinearisationContributionWithV}
    ].
proof.
  proc.
  inline Primops.mload.
  call (pointMulIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointAddAssign_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulIntoDest_extracted_equiv_low). wp.
  skip. rewrite /Constants.R. by progress.
qed.
