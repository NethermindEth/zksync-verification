require        Constants.
require import EvaluateLagrangePolyOutOfDomain.
require import LookupQuotientContribution.
require import PermutationQuotientContribution.
require import PurePrimops.
require import UInt256.
require import RevertWithMessage.
require import Verifier.
require import YulPrimops.

module VerifyQuotientEvaluation = {
  proc low(): unit = {
    var alpha, currentAlpha, stateZ, _12, _17, _20, _21, stateT, _23, result, _24, _25, _27, _28, _30, vanishing, _32, lhs;
    alpha <@ Primops.mload(W256.of_int 3520);
    currentAlpha <- (PurePrimops.mulmod alpha alpha (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 3616, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 3648, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 3680, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 3712, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 3744, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 3776, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 3808, currentAlpha);
    stateZ <@ Primops.mload(W256.of_int 4064);
    _12 <@ EvaluateLagrangePolyOutOfDomain.low(W256.zero, stateZ);
    Primops.mstore(W256.of_int 4128, _12);
    _17 <@ EvaluateLagrangePolyOutOfDomain.low((W256.of_int Constants.DOMAIN_SIZE) - W256.one, stateZ);
    Primops.mstore(W256.of_int 4160, _17);
    _20 <@ Primops.mload(W256.of_int 1824);
    _21 <@ Primops.mload(W256.of_int 4128);
    stateT <- (PurePrimops.mulmod _21 _20 (W256.of_int Constants.R));
    _23 <@ Primops.mload(W256.of_int 2720);
    result <- (PurePrimops.mulmod stateT _23 (W256.of_int Constants.R));
    _24 <@ PermutationQuotientContribution.low();
    result <- (PurePrimops.addmod result _24 (W256.of_int Constants.R));
    _25 <@ LookupQuotientContribution.low();
    result <- (PurePrimops.addmod result _25 (W256.of_int Constants.R));
    _27 <@ Primops.mload(W256.of_int 3104);
    result <- (PurePrimops.addmod _27 result (W256.of_int Constants.R));
    _28 <- ((W256.of_int Constants.R) - W256.one);
    _30 <@ Primops.mload(W256.of_int 4192);
    vanishing <- (PurePrimops.addmod _30 _28 (W256.of_int Constants.R));
    _32 <@ Primops.mload(W256.of_int 3072);
    lhs <- (PurePrimops.mulmod _32 vanishing (W256.of_int Constants.R));
    if ((bool_of_uint256 (PurePrimops.iszero (PurePrimops.eq_uint256 lhs result))))
    {
      RevertWithMessage.low(W256.of_int 27, W256.of_int STRING);
    }
  }
}.

lemma verifyQuotientEvaluation_extracted_equiv_low:
    equiv [
      Verifier.usr_verifyQuotientEvaluation ~ VerifyQuotientEvaluation.low:
      ={arg, glob VerifyQuotientEvaluation} ==>
      ={res, glob VerifyQuotientEvaluation}
    ].
    proc.
    seq 69 36: (#pre /\ usr_lhs{1} = lhs{2} /\ usr_result{1} = result{2}).
    wp.
    inline Primops.mload. wp.
    call lookupQuotientContribution_extracted_equiv_low. wp.
    call permutationQuotientContribution_extracted_equiv_low. wp.
    inline Primops.mstore. wp.
    call evaluateLagrangePolyOutOfDomain_extracted_equiv_low. wp.
    call evaluateLagrangePolyOutOfDomain_extracted_equiv_low. wp.
    skip.
    rewrite /Constants.R /Constants.DOMAIN_SIZE.
    by progress.
    sp.
    if. by progress.
    sp.
    call revertWithMessage_extracted_equiv_low. skip.
    by progress.
    skip.
    by progress.
  qed.








    
