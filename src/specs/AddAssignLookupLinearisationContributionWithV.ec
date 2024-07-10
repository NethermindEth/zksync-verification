require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module AddAssignLookupLinearisationContributionWithV = {
    proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256): unit = {
    var factor, _2, _3, _5, _9, _11, _13, fReconstructed, eta', currentEta, _15, _16, _18, _19, _21, _23, _25, _26, _27, _29, _31, _32, _34, _36, _37, _38;
    factor <@ Primops.mload(W256.of_int 2912);
    _2 <@ Primops.mload((W256.of_int 3744));
    factor <- (PurePrimops.mulmod factor _2 (W256.of_int Constants.R));
    _3 <@ Primops.mload((W256.of_int 4096));
    factor <- (PurePrimops.mulmod factor _3 (W256.of_int Constants.R));
    _5 <@ Primops.mload(W256.of_int 4000);
    factor <- (PurePrimops.mulmod factor _5 (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 4992, factor);
    factor <@ Primops.mload(W256.of_int 2976);
    _9 <@ Primops.mload(W256.of_int 3872);
    factor <- (PurePrimops.mulmod factor _9 (W256.of_int Constants.R));
    _11 <@ Primops.mload(W256.of_int 2944);
    factor <- (PurePrimops.addmod factor _11 (W256.of_int Constants.R));
    _13 <@ Primops.mload(W256.of_int 3968);
    factor <- (PurePrimops.addmod factor _13 (W256.of_int Constants.R));
    fReconstructed <- stateOpening0AtZ;
    eta' <@ Primops.mload(W256.of_int 3840);
    currentEta <- eta';
    _15 <- (PurePrimops.mulmod eta' stateOpening1AtZ (W256.of_int Constants.R));
    fReconstructed <- (PurePrimops.addmod stateOpening0AtZ _15 (W256.of_int Constants.R));
    currentEta <- (PurePrimops.mulmod eta' eta' (W256.of_int Constants.R));
    _16 <- (PurePrimops.mulmod currentEta stateOpening2AtZ (W256.of_int Constants.R));
    fReconstructed <- (PurePrimops.addmod fReconstructed _16 (W256.of_int Constants.R));
    currentEta <- (PurePrimops.mulmod currentEta eta' (W256.of_int Constants.R));
    _18 <@ Primops.mload(W256.of_int 3040);
    _19 <- (PurePrimops.mulmod _18 currentEta (W256.of_int Constants.R));
    fReconstructed <- (PurePrimops.addmod fReconstructed _19 (W256.of_int Constants.R));
    _21 <@ Primops.mload(W256.of_int 3008);
    fReconstructed <- (PurePrimops.mulmod fReconstructed _21 (W256.of_int Constants.R));
    _23 <@ Primops.mload(W256.of_int 3904);
    fReconstructed <- (PurePrimops.addmod fReconstructed _23 (W256.of_int Constants.R));
    factor <- (PurePrimops.mulmod factor fReconstructed (W256.of_int Constants.R));
    _25 <@ Primops.mload(W256.of_int 3936);
    factor <- (PurePrimops.mulmod factor _25 (W256.of_int Constants.R));
    factor <- ((W256.of_int Constants.R) - factor);
    _26 <@ Primops.mload((W256.of_int 3744));
    factor <- (PurePrimops.mulmod factor _26 (W256.of_int Constants.R));
    _27 <@ Primops.mload((W256.of_int 4096));
    factor <- (PurePrimops.mulmod factor _27 (W256.of_int Constants.R));
    _29 <@ Primops.mload(W256.of_int 3776);
    _31 <@ Primops.mload(W256.of_int 4128);
    _32 <- (PurePrimops.mulmod _31 _29 (W256.of_int Constants.R));
    factor <- (PurePrimops.addmod factor _32 (W256.of_int Constants.R));
    _34 <@ Primops.mload(W256.of_int 3808);
    _36 <@ Primops.mload(W256.of_int 4160);
    _37 <- (PurePrimops.mulmod _36 _34 (W256.of_int Constants.R));
    factor <- (PurePrimops.addmod factor _37 (W256.of_int Constants.R));
    _38 <@ Primops.mload(W256.of_int 4000);
    factor <- (PurePrimops.mulmod factor _38 (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 4960, factor);
  }
}.

lemma addAssignLookupLinearisationContributionWithV_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_addAssignLookupLinearisationContributionWithV ~ AddAssignLookupLinearisationContributionWithV.low :
      ={arg, glob AddAssignLookupLinearisationContributionWithV} ==>
      ={res, glob AddAssignLookupLinearisationContributionWithV}
    ].
proof.
  proc.
  inline*.
  wp.
  skip.
  rewrite /Constants.R.
  by progress.
qed.
    
      
