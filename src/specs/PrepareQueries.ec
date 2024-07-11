pragma Goals:printall.

require import AddAssignPermutationLinearisationContributionWithV.
require import AddAssignRescueCustomGateLinearisationContributionWithV.
require import AddAssignLookupLinearisationContributionWithV.
require import MainGateLinearisationContributionWithV.
require import PointMulAndAddIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module PrepareQueries = {
  proc low(): unit = {
    var _1, zInDomainSize, currentZ, _3, _6, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ, _18, _21, eta', currentEta;
    _1 <- ();
    zInDomainSize <@ Primops.mload(W256.of_int 4192);
    currentZ <- zInDomainSize;
    _3 <@ Primops.mload(W256.of_int 2304);
    Primops.mstore(W256.of_int 4288, _3);
    _6 <@ Primops.mload(W256.of_int 2336);
    Primops.mstore(W256.of_int 4320, _6);
    PointMulAndAddIntoDest.low(W256.of_int 2368, zInDomainSize, W256.of_int 4288);
    currentZ <- (PurePrimops.mulmod zInDomainSize zInDomainSize (W256.of_int Constants.R));
    PointMulAndAddIntoDest.low(W256.of_int 2432, currentZ, W256.of_int 4288);
    currentZ <- (PurePrimops.mulmod currentZ zInDomainSize (W256.of_int Constants.R));
    PointMulAndAddIntoDest.low(W256.of_int 2496, currentZ, W256.of_int 4288);
    stateOpening0AtZ <@ Primops.mload(W256.of_int 2560);
    stateOpening1AtZ <@ Primops.mload(W256.of_int 2592);
    stateOpening2AtZ <@ Primops.mload(W256.of_int 2624);
    stateOpening3AtZ <@ Primops.mload(W256.of_int 2656);
    MainGateLinearisationContributionWithV.low(W256.of_int 4352, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ);
    AddAssignRescueCustomGateLinearisationContributionWithV.low(W256.of_int 4352, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ);
    AddAssignPermutationLinearisationContributionWithV.low(W256.of_int 4352, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ);
    AddAssignLookupLinearisationContributionWithV.low(W256.of_int 4352, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ);
    _18 <@ Primops.mload(W256.of_int 1472);
    Primops.mstore(W256.of_int 4416, _18);
    _21 <@ Primops.mload(W256.of_int 1504);
    Primops.mstore(W256.of_int 4448, _21);
    eta' <@ Primops.mload(W256.of_int 3840);
    currentEta <- eta';
    PointMulAndAddIntoDest.low(W256.of_int 1536, eta', W256.of_int 4416);
    currentEta <- (PurePrimops.mulmod eta' eta' (W256.of_int Constants.R));
    PointMulAndAddIntoDest.low(W256.of_int 1600, currentEta, W256.of_int 4416);
    currentEta <- (PurePrimops.mulmod currentEta eta' (W256.of_int Constants.R));
    PointMulAndAddIntoDest.low(W256.of_int 1664, currentEta, W256.of_int 4416);
  }
}.

lemma prepareQueries_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_prepareQueries ~ PrepareQueries.low:
      ={arg, glob PrepareQueries} ==>
      ={res, glob PrepareQueries}
    ].
    proof.
      proc.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      inline Primops.mload Primops.mstore. wp.
      call addAssignLookupLinearisationContributionWithV_extracted_equiv_low.
      call addAssignPermutationLinearisationContributionWithV_extracted_equiv_low.
      call addAssignRescueCustomGateLinearisationContributionWithV_extracted_equiv_low.
      call mainGateLinearisationContributionWithV_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      skip. rewrite /Constants.R. by progress.
    qed.

    
