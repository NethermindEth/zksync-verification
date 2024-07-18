require        Constants.
require import EvaluateLagrangePolyOutOfDomain.
require import LookupQuotientContribution.
require import PermutationQuotientContribution.
require import PurePrimops.
require import UInt256.
require import RevertWithMessage.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module VerifyQuotientEvaluation = {
  proc low(): unit = {
    var alpha, currentAlpha, stateZ, _12, _17, _20, _21, stateT, _23, result, _24, _25, _27, _28, _30, vanishing, _32, lhs;
    alpha <@ Primops.mload(STATE_ALPHA_SLOT);
    currentAlpha <- (PurePrimops.mulmod alpha alpha R_MOD);
    Primops.mstore(STATE_POWER_OF_ALPHA_2_SLOT, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha R_MOD);
    Primops.mstore(STATE_POWER_OF_ALPHA_3_SLOT, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha R_MOD);
    Primops.mstore(STATE_POWER_OF_ALPHA_4_SLOT, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha R_MOD);
    Primops.mstore(STATE_POWER_OF_ALPHA_5_SLOT, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha R_MOD);
    Primops.mstore(STATE_POWER_OF_ALPHA_6_SLOT, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha R_MOD);
    Primops.mstore(STATE_POWER_OF_ALPHA_7_SLOT, currentAlpha);
    currentAlpha <- (PurePrimops.mulmod currentAlpha alpha R_MOD);
    Primops.mstore(STATE_POWER_OF_ALPHA_8_SLOT, currentAlpha);
    stateZ <@ Primops.mload(STATE_Z_SLOT);
    _12 <@ EvaluateLagrangePolyOutOfDomain.low(W256.zero, stateZ);
    Primops.mstore(STATE_L_0_AT_Z_SLOT, _12);
    _17 <@ EvaluateLagrangePolyOutOfDomain.low((DOMAIN_SIZE) - W256.one, stateZ);
    Primops.mstore(STATE_L_N_MINUS_ONE_AT_Z_SLOT, _17);
    _20 <@ Primops.mload(PROOF_PUBLIC_INPUT);
    _21 <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    stateT <- (PurePrimops.mulmod _21 _20 R_MOD);
    _23 <@ Primops.mload(PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT);
    result <- (PurePrimops.mulmod stateT _23 R_MOD);
    _24 <@ PermutationQuotientContribution.low();
    result <- (PurePrimops.addmod result _24 R_MOD);
    _25 <@ LookupQuotientContribution.low();
    result <- (PurePrimops.addmod result _25 R_MOD);
    _27 <@ Primops.mload(PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT);
    result <- (PurePrimops.addmod _27 result R_MOD);
    _28 <- (R_MOD - W256.one);
    _30 <@ Primops.mload(STATE_Z_IN_DOMAIN_SIZE);
    vanishing <- (PurePrimops.addmod _30 _28 R_MOD);
    _32 <@ Primops.mload(PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT);
    lhs <- (PurePrimops.mulmod _32 vanishing R_MOD);
    if ((bool_of_uint256 (PurePrimops.iszero (PurePrimops.eq_uint256 lhs result))))
    {
      RevertWithMessage.low(W256.of_int 27, W256.of_int STRING);
    }
  }
}.

lemma verifyQuotientEvaluation_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_verifyQuotientEvaluation ~ VerifyQuotientEvaluation.low:
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








    
