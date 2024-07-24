require        Constants.
require import Modexp.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module LookupQuotientContribution = {
  proc low(): uint256 = {
    var ret, betaLookup, gammaLookup, betaPlusOne, betaGamma, _8, _10, _12, lastOmega, _18, zMinusLastOmega, _21, _23, intermediateValue, lnMinusOneAtZ, betaGammaPowered, alphaPower8, _27, subtrahend;
    betaLookup <@ Primops.mload(STATE_BETA_LOOKUP_SLOT);
    gammaLookup <@ Primops.mload(STATE_GAMMA_LOOKUP_SLOT);
    betaPlusOne <- (PurePrimops.addmod betaLookup W256.one R_MOD);
    betaGamma <- (PurePrimops.mulmod betaPlusOne gammaLookup R_MOD);
    Primops.mstore(STATE_BETA_PLUS_ONE_SLOT, betaPlusOne);
    Primops.mstore(STATE_BETA_GAMMA_PLUS_GAMMA_SLOT, betaGamma);
    _8 <@ Primops.mload(PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT);
    ret <- (PurePrimops.mulmod _8 betaLookup R_MOD);
    ret <- (PurePrimops.addmod ret betaGamma R_MOD);
    _10 <@ Primops.mload(PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    ret <- (PurePrimops.mulmod ret _10 R_MOD);
    _12 <@ Primops.mload(STATE_POWER_OF_ALPHA_6_SLOT);
    ret <- (PurePrimops.mulmod ret _12 R_MOD);
    lastOmega <@ Modexp.low(OMEGA, (DOMAIN_SIZE) - W256.one);
    _18 <@ Primops.mload(STATE_Z_SLOT);
    zMinusLastOmega <- (PurePrimops.addmod _18 (R_MOD - lastOmega) R_MOD);
    Primops.mstore(STATE_Z_MINUS_LAST_OMEGA_SLOT, zMinusLastOmega);
    ret <- (PurePrimops.mulmod ret zMinusLastOmega R_MOD);
    _21 <@ Primops.mload(STATE_POWER_OF_ALPHA_7_SLOT);
    _23 <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    intermediateValue <- (PurePrimops.mulmod _23 _21 R_MOD);
    ret <- (PurePrimops.addmod ret (R_MOD - intermediateValue) R_MOD);
    lnMinusOneAtZ <@ Primops.mload(STATE_L_N_MINUS_ONE_AT_Z_SLOT);
    betaGammaPowered <@ Modexp.low(betaGamma, (DOMAIN_SIZE) - W256.one);
    alphaPower8 <@ Primops.mload(STATE_POWER_OF_ALPHA_8_SLOT);
    _27 <- (PurePrimops.mulmod lnMinusOneAtZ betaGammaPowered R_MOD);
    subtrahend <- (PurePrimops.mulmod _27 alphaPower8 R_MOD);
    ret <- (PurePrimops.addmod ret (R_MOD - subtrahend) R_MOD);
    return ret;
  }
}.

lemma lookupQuotientContribution_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_lookupQuotientContribution ~ LookupQuotientContribution.low:
      ={arg, glob LookupQuotientContribution} ==>
      ={res, glob LookupQuotientContribution}
    ].
      proc.
      sp.
      seq 2 1: (#pre /\ usr_betaLookup{1} = betaLookup{2}). inline*. wp. skip. by progress.
      seq 3 1: (#pre /\ usr_gammaLookup{1} = gammaLookup{2}). inline*. wp. skip. by progress.
      cfold{1} 1.
      seq 2 1: (#pre /\ usr_betaPlusOne{1} = betaPlusOne{2} /\ _4{1} = W256.one). inline*. wp. skip. rewrite /Constants.R. by progress.
      seq 1 1: (#pre /\ usr_betaGamma{1} = betaGamma{2}). wp. skip. rewrite /Constants.R. by progress.
      seq 17 9: (#pre /\ usr_res{1} = ret{2}). inline*. wp. skip. rewrite /Constants.R. by progress.
      seq 5 1: (#pre /\ usr_lastOmega{1} = lastOmega{2} /\ _14{1} = ((DOMAIN_SIZE) - W256.one)). sp. wp. call modexp_extracted_equiv_low. skip. rewrite /Constants.OMEGA /Constants.DOMAIN_SIZE. by progress.
      seq 5 2: (#pre /\ usr_zMinusLastOmega{1} = zMinusLastOmega{2}). inline*. wp. skip. rewrite /Constants.R. by progress.
      seq 10 5: (#pre /\ usr_intermediateValue{1} = intermediateValue{2}). inline*. wp. skip. rewrite /Constants.R. by progress.
      seq 5 2: (#pre /\ usr_lnMinusOneAtZ{1} = lnMinusOneAtZ{2}). inline*. wp. skip. rewrite /Constants.R. by progress.
      seq 2 1: (#pre /\ usr_betaGammaPowered{1} = betaGammaPowered{2}). wp. call modexp_extracted_equiv_low. skip. progress. rewrite /Constants.DOMAIN_SIZE. by progress.
      seq 3 1: (#pre /\ usr_alphaPower8{1} = alphaPower8{2}). inline*. wp. skip. by progress.
      seq 2 2: (#pre /\ usr_subtrahend{1} = subtrahend{2}). wp. skip. rewrite /Constants.R. by progress.
      wp. skip. rewrite /Constants.R. by progress.
    qed.
