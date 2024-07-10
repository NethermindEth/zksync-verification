require        Constants.
require import PointMulIntoDest.
require import PointSubAssign.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module AddAssignPermutationLinearisationContributionWithV = {
  proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256, stateOpening3AtZ : uint256): unit = {
    var factor, _1, _3, gamma, _4, intermediateValue, _6, _7, _9, _10, _12, _13, l0AtZ, _16, _17, _18, _20, _21, _23, beta', gamma_1, _25, _26, _27, intermediateValue_1, _29, _30, _31, _33, _34, _35, _36;
    factor <@ Primops.mload((W256.of_int 3680));
    _1 <@ Primops.mload((W256.of_int 3552));
    _3 <@ Primops.mload(W256.of_int 4064);
    gamma <@ Primops.mload((W256.of_int 3584));
    _4 <- (PurePrimops.addmod (PurePrimops.mulmod _3 _1 (W256.of_int Constants.R)) gamma (W256.of_int Constants.R));
    intermediateValue <- (PurePrimops.addmod _4 stateOpening0AtZ (W256.of_int Constants.R));
    factor <- (PurePrimops.mulmod factor intermediateValue (W256.of_int Constants.R));
    _6 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 (W256.of_int Constants.R)) (W256.of_int 5) (W256.of_int Constants.R));
    _7 <- (PurePrimops.addmod _6 gamma (W256.of_int Constants.R));
    intermediateValue <- (PurePrimops.addmod _7 stateOpening1AtZ (W256.of_int Constants.R));
    factor <- (PurePrimops.mulmod factor intermediateValue (W256.of_int Constants.R));
    _9 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 (W256.of_int Constants.R)) (W256.of_int 7) (W256.of_int Constants.R));
    _10 <- (PurePrimops.addmod _9 gamma (W256.of_int Constants.R));
    intermediateValue <- (PurePrimops.addmod _10 stateOpening2AtZ (W256.of_int Constants.R));
    factor <- (PurePrimops.mulmod factor intermediateValue (W256.of_int Constants.R));
    _12 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 (W256.of_int Constants.R)) (W256.of_int 10) (W256.of_int Constants.R));
    _13 <- (PurePrimops.addmod _12 gamma (W256.of_int Constants.R));
    intermediateValue <- (PurePrimops.addmod _13 stateOpening3AtZ (W256.of_int Constants.R));
    factor <- (PurePrimops.mulmod factor intermediateValue (W256.of_int Constants.R));
    l0AtZ <@ Primops.mload(W256.of_int 4128);
    _16 <@ Primops.mload(W256.of_int 3712);
    _17 <- (PurePrimops.mulmod l0AtZ _16 (W256.of_int Constants.R));
    factor <- (PurePrimops.addmod factor _17 (W256.of_int Constants.R));
    _18 <@ Primops.mload((W256.of_int 4000));
    factor <- (PurePrimops.mulmod factor _18 (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 4928, factor);
    _20 <@ Primops.mload((W256.of_int 3552));
    _21 <@ Primops.mload((W256.of_int 3680));
    factor <- (PurePrimops.mulmod _21 _20 (W256.of_int Constants.R));
    _23 <@ Primops.mload(W256.of_int 2848);
    factor <- (PurePrimops.mulmod factor _23 (W256.of_int Constants.R));
    beta' <@ Primops.mload((W256.of_int 3552));
    gamma_1 <@ Primops.mload((W256.of_int 3584));
    _25 <@ Primops.mload(W256.of_int 2752);
    _26 <- (PurePrimops.mulmod _25 beta' (W256.of_int Constants.R));
    _27 <- (PurePrimops.addmod _26 gamma_1 (W256.of_int Constants.R));
    intermediateValue_1 <- (PurePrimops.addmod _27 stateOpening0AtZ (W256.of_int Constants.R));
    factor <- (PurePrimops.mulmod factor intermediateValue_1 (W256.of_int Constants.R));
    _29 <@ Primops.mload(W256.of_int 2784);
    _30 <- (PurePrimops.mulmod _29 beta' (W256.of_int Constants.R));
    _31 <- (PurePrimops.addmod _30 gamma_1 (W256.of_int Constants.R));
    intermediateValue_1 <- (PurePrimops.addmod _31 stateOpening1AtZ (W256.of_int Constants.R));
    factor <- (PurePrimops.mulmod factor intermediateValue_1 (W256.of_int Constants.R));
    _33 <@ Primops.mload(W256.of_int 2816);
    _34 <- (PurePrimops.mulmod _33 beta' (W256.of_int Constants.R));
    _35 <- (PurePrimops.addmod _34 gamma_1 (W256.of_int Constants.R));
    intermediateValue_1 <- (PurePrimops.addmod _35 stateOpening2AtZ (W256.of_int Constants.R));
    factor <- (PurePrimops.mulmod factor intermediateValue_1 (W256.of_int Constants.R));
    _36 <@ Primops.mload((W256.of_int 4000));
    factor <- (PurePrimops.mulmod factor _36 (W256.of_int Constants.R));
    PointMulIntoDest.low(W256.of_int 1344, factor, W256.of_int 4224);
    PointSubAssign.low(dest, W256.of_int 4224);
  }
}.

lemma addAssignPermutationLinearisationContributionWithV_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_addAssignPermutationLinearisationContributionWithV ~ AddAssignPermutationLinearisationContributionWithV.low :
      ={arg, glob AddAssignPermutationLinearisationContributionWithV} ==>
      ={res, glob AddAssignPermutationLinearisationContributionWithV}
    ].
proof.
  proc.
  call (pointSubAssign_extracted_equiv_low). wp.
  call (pointMulIntoDest_extracted_equiv_low).
  inline*. wp. skip. rewrite /Constants.R. by progress.
qed.
