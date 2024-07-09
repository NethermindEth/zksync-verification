require        Constants.
require import Modexp.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module LookupQuotientContribution = {
  proc low(): uint256 = {
    var ret, betaLookup, gammaLookup, betaPlusOne, betaGamma, _8, _10, _12, lastOmega, _18, zMinusLastOmega, _21, _23, intermediateValue, lnMinusOneAtZ, betaGammaPowered, alphaPower8, _27, subtrahend;
    betaLookup <@ Primops.mload(W256.of_int 3872);
    gammaLookup <@ Primops.mload(W256.of_int 3904);
    betaPlusOne <- (PurePrimops.addmod betaLookup W256.one (W256.of_int Constants.R));
    betaGamma <- (PurePrimops.mulmod betaPlusOne gammaLookup (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 3936, betaPlusOne);
    Primops.mstore(W256.of_int 3968, betaGamma);
    _8 <@ Primops.mload(W256.of_int 2880);
    ret <- (PurePrimops.mulmod _8 betaLookup (W256.of_int Constants.R));
    ret <- (PurePrimops.addmod ret betaGamma (W256.of_int Constants.R));
    _10 <@ Primops.mload(W256.of_int 2912);
    ret <- (PurePrimops.mulmod ret _10 (W256.of_int Constants.R));
    _12 <@ Primops.mload(W256.of_int 3744);
    ret <- (PurePrimops.mulmod ret _12 (W256.of_int Constants.R));
    lastOmega <@ Modexp.low(W256.of_int Constants.OMEGA, (W256.of_int Constants.DOMAIN_SIZE) - W256.one);
    _18 <@ Primops.mload(W256.of_int 4064);
    zMinusLastOmega <- (PurePrimops.addmod _18 ((W256.of_int Constants.R) - lastOmega) (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 4096, zMinusLastOmega);
    ret <- (PurePrimops.mulmod ret zMinusLastOmega (W256.of_int Constants.R));
    _21 <@ Primops.mload(W256.of_int 3776);
    _23 <@ Primops.mload(W256.of_int 4128);
    intermediateValue <- (PurePrimops.mulmod _23 _21 (W256.of_int Constants.R));
    ret <- (PurePrimops.addmod ret ((W256.of_int Constants.R) - intermediateValue) (W256.of_int Constants.R));
    lnMinusOneAtZ <@ Primops.mload(W256.of_int 4160);
    betaGammaPowered <@ Modexp.low(betaGamma, (W256.of_int Constants.DOMAIN_SIZE) - W256.one);
    alphaPower8 <@ Primops.mload(W256.of_int 3808);
    _27 <- (PurePrimops.mulmod lnMinusOneAtZ betaGammaPowered (W256.of_int Constants.R));
    subtrahend <- (PurePrimops.mulmod _27 alphaPower8 (W256.of_int Constants.R));
    ret <- (PurePrimops.addmod ret ((W256.of_int Constants.R) - subtrahend) (W256.of_int Constants.R));
    return ret;
  }
}.

lemma lookupQuotientContribution_extracted_equiv_low:
    equiv [
      Verifier.usr_lookupQuotientContribution ~ LookupQuotientContribution.low:
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
      seq 5 1: (#pre /\ usr_lastOmega{1} = lastOmega{2} /\ _14{1} = ((W256.of_int 67108864) - W256.one)). sp. wp. call modexp_extracted_equiv_low. skip. rewrite /Constants.OMEGA /Constants.DOMAIN_SIZE. by progress.
      seq 5 2: (#pre /\ usr_zMinusLastOmega{1} = zMinusLastOmega{2}). inline*. wp. skip. rewrite /Constants.R. by progress.
      seq 10 5: (#pre /\ usr_intermediateValue{1} = intermediateValue{2}). inline*. wp. skip. rewrite /Constants.R. by progress.
      seq 5 2: (#pre /\ usr_lnMinusOneAtZ{1} = lnMinusOneAtZ{2}). inline*. wp. skip. rewrite /Constants.R. by progress.
      seq 2 1: (#pre /\ usr_betaGammaPowered{1} = betaGammaPowered{2}). wp. call modexp_extracted_equiv_low. skip. progress. rewrite /Constants.DOMAIN_SIZE. by progress.
      seq 3 1: (#pre /\ usr_alphaPower8{1} = alphaPower8{2}). inline*. wp. skip. by progress.
      seq 2 2: (#pre /\ usr_subtrahend{1} = subtrahend{2}). wp. skip. rewrite /Constants.R. by progress.
      wp. skip. rewrite /Constants.R. by progress.
    qed.
