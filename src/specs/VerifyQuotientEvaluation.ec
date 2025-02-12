require import AllCore.
require import IntDiv.
require        Constants.
require import EvaluateLagrangePolyOutOfDomain.
require import Field.
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

  proc mid (
      stateAlpha
      stateBeta
      stateBetaLookup
      stateGamma
      stateGammaLookup
      stateZ
      proofPublicInput
      proofCopyPermutationPolys0OpeningAtZ
      proofCopyPermutationPolys1OpeningAtZ
      proofCopyPermutationPolys2OpeningAtZ
      proofStatePolys0OpeningAtZ
      proofStatePolys1OpeningAtZ
      proofStatePolys2OpeningAtZ
      proofStatePolys3OpeningAtZ
      proofLookupSPolyOpeningAtZOmega
      proofLookupGrandProductOpeningAtZOmega
      proofGateSelectors0OpeningAtZ
      proofLinearisationPolyOpeningAtZ
      proofCopyPermutationGrandProductOpeningAtZOmega
      stateZInDomainSize
      proofQuotientPolyOpeningAtZ : int) :
  (bool option * int * int * int * int * int * int * int * int * int * int * int * int) = {
    var r, elpodL0, elpodLn, stateT, pgsT, pqc, pqcR, lqc, lqcR, plpo, vanishing, lhs;
    var statePowerOfAlpha2, statePowerOfAlpha3, statePowerOfAlpha4, statePowerOfAlpha5,
        statePowerOfAlpha6, statePowerOfAlpha7, statePowerOfAlpha8 : int;
    var stateL0AtZ, stateLnMinusOneAtZ, stateBetaPlusOne,
        stateBetaGammaPlusGamma, stateZMinusLastOmega : int;

    statePowerOfAlpha2 <- stateAlpha^2 %% Constants.R;
    statePowerOfAlpha3 <- stateAlpha^3 %% Constants.R;
    statePowerOfAlpha4 <- stateAlpha^4 %% Constants.R;
    statePowerOfAlpha5 <- stateAlpha^5 %% Constants.R;
    statePowerOfAlpha6 <- stateAlpha^6 %% Constants.R;
    statePowerOfAlpha7 <- stateAlpha^7 %% Constants.R;
    statePowerOfAlpha8 <- stateAlpha^8 %% Constants.R;

    elpodL0 <@ EvaluateLagrangePolyOutOfDomain.mid(0, stateZ);
    
    if (elpodL0 = None) {
      r <- None;
      stateBetaGammaPlusGamma <- 0;
      stateBetaPlusOne <- 0;
      stateL0AtZ <- 0;
      stateLnMinusOneAtZ <- 0;
      stateZMinusLastOmega <- 0;
    } else {
      stateL0AtZ <- oget(elpodL0);
      elpodLn <@ EvaluateLagrangePolyOutOfDomain.mid((Constants.DOMAIN_SIZE - 1), stateZ);

      (* Since the fist one didn't failed neither the second will *)
      stateLnMinusOneAtZ <- oget(elpodLn);
      stateT <- (stateL0AtZ * proofPublicInput) %% Constants.R;
      pgsT <- (stateT * proofGateSelectors0OpeningAtZ) %% Constants.R;
      pqc <@ PermutationQuotientContribution.mid(
                statePowerOfAlpha4,
                statePowerOfAlpha5,
                proofCopyPermutationGrandProductOpeningAtZOmega,
                stateBeta,
                stateGamma,
                proofCopyPermutationPolys0OpeningAtZ,
                proofCopyPermutationPolys1OpeningAtZ,
                proofCopyPermutationPolys2OpeningAtZ,
                proofStatePolys0OpeningAtZ,
                proofStatePolys1OpeningAtZ,
                proofStatePolys2OpeningAtZ,
                proofStatePolys3OpeningAtZ,
                stateL0AtZ);
      pqcR <- (pgsT + pqc) %% Constants.R;  

      (lqc, stateBetaPlusOne, stateBetaGammaPlusGamma, stateZMinusLastOmega) <@
        LookupQuotientContribution.mid(
           stateBetaLookup,
           stateGammaLookup,
           statePowerOfAlpha6,
           statePowerOfAlpha7,
           statePowerOfAlpha8,
           proofLookupSPolyOpeningAtZOmega,
           proofLookupGrandProductOpeningAtZOmega,
           stateZ,
           stateL0AtZ,
           stateLnMinusOneAtZ);

      lqcR <- (pqcR + lqc) %% Constants.R;
      plpo <- (proofLinearisationPolyOpeningAtZ + lqcR) %% Constants.R;
      vanishing <- (stateZInDomainSize + (Constants.R - 1)) %% Constants.R;
      lhs <- (proofQuotientPolyOpeningAtZ * vanishing) %% Constants.R;
      r <- Some (lhs = plpo);
    }
    
    return (r,
      statePowerOfAlpha2,
      statePowerOfAlpha3,
      statePowerOfAlpha4,
      statePowerOfAlpha5,
      statePowerOfAlpha6, 
      statePowerOfAlpha7,
      statePowerOfAlpha8,
      stateL0AtZ,
      stateLnMinusOneAtZ,
      stateBetaPlusOne,
      stateBetaGammaPlusGamma,
      stateZMinusLastOmega
    );
  }

  proc high_encapsulated (
      stateAlpha
      stateBeta
      stateBetaLookup
      stateGamma
      stateGammaLookup
      stateZ
      proofPublicInput
      proofCopyPermutationPolys0OpeningAtZ
      proofCopyPermutationPolys1OpeningAtZ
      proofCopyPermutationPolys2OpeningAtZ
      proofStatePolys0OpeningAtZ
      proofStatePolys1OpeningAtZ
      proofStatePolys2OpeningAtZ
      proofStatePolys3OpeningAtZ
      proofLookupSPolyOpeningAtZOmega
      proofLookupGrandProductOpeningAtZOmega
      proofGateSelectors0OpeningAtZ
      proofLinearisationPolyOpeningAtZ
      proofCopyPermutationGrandProductOpeningAtZOmega
      stateZInDomainSize
      proofQuotientPolyOpeningAtZ : FieldR.F) :
  (bool option * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F) = {
    var r, elpodL0, elpodLn, pqc, lqc;
    var statePowerOfAlpha2, statePowerOfAlpha3, statePowerOfAlpha4, statePowerOfAlpha5,
        statePowerOfAlpha6, statePowerOfAlpha7, statePowerOfAlpha8 : FieldR.F;
    var stateL0AtZ, stateLnMinusOneAtZ, stateBetaPlusOne,
        stateBetaGammaPlusGamma, stateZMinusLastOmega : FieldR.F;

    statePowerOfAlpha2 <- stateAlpha^2;
    statePowerOfAlpha3 <- stateAlpha^3;
    statePowerOfAlpha4 <- stateAlpha^4;
    statePowerOfAlpha5 <- stateAlpha^5;
    statePowerOfAlpha6 <- stateAlpha^6;
    statePowerOfAlpha7 <- stateAlpha^7;
    statePowerOfAlpha8 <- stateAlpha^8;

    elpodL0 <@ EvaluateLagrangePolyOutOfDomain.high(0, stateZ);
    
    if (elpodL0 = None) {
      r <- None;
      stateBetaGammaPlusGamma <- FieldR.zero;
      stateBetaPlusOne <- FieldR.zero;
      stateL0AtZ <- FieldR.zero;
      stateLnMinusOneAtZ <- FieldR.zero;
      stateZMinusLastOmega <- FieldR.zero;
    } else {
      stateL0AtZ <- oget(elpodL0);
      elpodLn <@ EvaluateLagrangePolyOutOfDomain.high((Constants.DOMAIN_SIZE - 1), stateZ);

      (* Since the fist one didn't failed neither the second will *)
      stateLnMinusOneAtZ <- oget(elpodLn);

      pqc <@ PermutationQuotientContribution.high(
                statePowerOfAlpha4,
                statePowerOfAlpha5,
                proofCopyPermutationGrandProductOpeningAtZOmega,
                stateBeta,
                stateGamma,
                proofCopyPermutationPolys0OpeningAtZ,
                proofCopyPermutationPolys1OpeningAtZ,
                proofCopyPermutationPolys2OpeningAtZ,
                proofStatePolys0OpeningAtZ,
                proofStatePolys1OpeningAtZ,
                proofStatePolys2OpeningAtZ,
                proofStatePolys3OpeningAtZ,
                stateL0AtZ);

      (lqc, stateBetaPlusOne, stateBetaGammaPlusGamma, stateZMinusLastOmega) <@
        LookupQuotientContribution.high(
           stateBetaLookup,
           stateGammaLookup,
           statePowerOfAlpha6,
           statePowerOfAlpha7,
           statePowerOfAlpha8,
           proofLookupSPolyOpeningAtZOmega,
           proofLookupGrandProductOpeningAtZOmega,
           stateZ,
           stateL0AtZ,
           stateLnMinusOneAtZ);

        r <- Some ((proofQuotientPolyOpeningAtZ * (stateZInDomainSize - FieldR.one)) 
         = (proofLinearisationPolyOpeningAtZ + stateL0AtZ * proofPublicInput * proofGateSelectors0OpeningAtZ + pqc + lqc));
    }
    
    return (r,
      statePowerOfAlpha2,
      statePowerOfAlpha3,
      statePowerOfAlpha4,
      statePowerOfAlpha5,
      statePowerOfAlpha6, 
      statePowerOfAlpha7,
      statePowerOfAlpha8,
      stateL0AtZ,
      stateLnMinusOneAtZ,
      stateBetaPlusOne,
      stateBetaGammaPlusGamma,
      stateZMinusLastOmega
    );
  }

 proc high' (
      stateAlpha
      stateBeta
      stateBetaLookup
      stateGamma
      stateGammaLookup
      stateZ
      proofPublicInput
      proofCopyPermutationPolys0OpeningAtZ
      proofCopyPermutationPolys1OpeningAtZ
      proofCopyPermutationPolys2OpeningAtZ
      proofStatePolys0OpeningAtZ
      proofStatePolys1OpeningAtZ
      proofStatePolys2OpeningAtZ
      proofStatePolys3OpeningAtZ
      proofLookupSPolyOpeningAtZOmega
      proofLookupGrandProductOpeningAtZOmega
      proofGateSelectors0OpeningAtZ
      proofLinearisationPolyOpeningAtZ
      proofCopyPermutationGrandProductOpeningAtZOmega
      stateZInDomainSize
      proofQuotientPolyOpeningAtZ : FieldR.F) :
  (bool option * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F) = {
    var r, pqc, lqc;
    var statePowerOfAlpha2, statePowerOfAlpha3, statePowerOfAlpha4, statePowerOfAlpha5,
        statePowerOfAlpha6, statePowerOfAlpha7, statePowerOfAlpha8 : FieldR.F;
    var stateL0AtZ, stateLnMinusOneAtZ, stateBetaPlusOne,
        stateBetaGammaPlusGamma, stateZMinusLastOmega : FieldR.F;
    var atDomainSize, stateZAtDomainSize : FieldR.F;

    statePowerOfAlpha2 <- stateAlpha^2;
    statePowerOfAlpha3 <- stateAlpha^3;
    statePowerOfAlpha4 <- stateAlpha^4;
    statePowerOfAlpha5 <- stateAlpha^5;
    statePowerOfAlpha6 <- stateAlpha^6;
    statePowerOfAlpha7 <- stateAlpha^7;
    statePowerOfAlpha8 <- stateAlpha^8;

    stateZAtDomainSize <- stateZ^Constants.DOMAIN_SIZE;

    if (stateZAtDomainSize = FieldR.one) {
      r <- None;
      stateBetaGammaPlusGamma <- FieldR.zero;
      stateBetaPlusOne <- FieldR.zero;
      stateL0AtZ <- FieldR.zero;
      stateLnMinusOneAtZ <- FieldR.zero;
      stateZMinusLastOmega <- FieldR.zero;
    } else {
      stateL0AtZ <- (stateZAtDomainSize - FieldR.one) * ((Constants.DOMAIN_SIZEFr * (stateZ - FieldR.one)) ^ (- 1));
      stateLnMinusOneAtZ <- (Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1) * (stateZAtDomainSize - FieldR.one)) * ((Constants.DOMAIN_SIZEFr * (stateZ - Constants.OMEGAFr^(Constants.DOMAIN_SIZE- 1))) ^ (- 1)); 

      pqc <- -statePowerOfAlpha4 * proofCopyPermutationGrandProductOpeningAtZOmega 
         * (proofCopyPermutationPolys0OpeningAtZ * stateBeta + stateGamma + proofStatePolys0OpeningAtZ) 
         * (proofCopyPermutationPolys1OpeningAtZ * stateBeta + stateGamma + proofStatePolys1OpeningAtZ) 
         * (proofCopyPermutationPolys2OpeningAtZ * stateBeta + stateGamma + proofStatePolys2OpeningAtZ) 
         * (proofStatePolys3OpeningAtZ + stateGamma)
      -statePowerOfAlpha5 * stateL0AtZ;

      (lqc, stateBetaPlusOne, stateBetaGammaPlusGamma, stateZMinusLastOmega) <- (
      ((statePowerOfAlpha6 * (proofLookupSPolyOpeningAtZOmega * stateBetaLookup + stateGammaLookup * (stateBetaLookup + FieldR.one)) * proofLookupGrandProductOpeningAtZOmega) * (stateZ - Constants.OMEGAFr ^(Constants.DOMAIN_SIZE - 1)) 
        - statePowerOfAlpha7 * stateL0AtZ 
        - statePowerOfAlpha8 * stateLnMinusOneAtZ * (stateGammaLookup * (stateBetaLookup + FieldR.one)) ^ (Constants.DOMAIN_SIZE - 1)), 
        (stateBetaLookup + FieldR.one), 
        stateGammaLookup * (stateBetaLookup + FieldR.one), 
        stateZ - Constants.OMEGAFr ^(Constants.DOMAIN_SIZE - 1));

        r <- Some ((proofQuotientPolyOpeningAtZ * (stateZInDomainSize - FieldR.one)) 
         = (proofLinearisationPolyOpeningAtZ + stateL0AtZ * proofPublicInput * proofGateSelectors0OpeningAtZ + pqc + lqc));
    }
    
    return (r,
      statePowerOfAlpha2,
      statePowerOfAlpha3,
      statePowerOfAlpha4,
      statePowerOfAlpha5,
      statePowerOfAlpha6, 
      statePowerOfAlpha7,
      statePowerOfAlpha8,
      stateL0AtZ,
      stateLnMinusOneAtZ,
      stateBetaPlusOne,
      stateBetaGammaPlusGamma,
      stateZMinusLastOmega
    );
  }

  (* r_0 = alpha^0 * L_0(z) * PI * q_{main selector}(z) + r(z)         -- main gate contribution
    
         - alpha^4 * z_perm(z*omega)(sigma_0(z) * beta + gamma + a(z)) \
                               (sigma_1(z) * beta + gamma + b(z))      |
                               (sigma_2(z) * beta + gamma + c(z))      | - permutation contribution
                               (sigma_3(z) + gamma)                    |
         - alpha^5 * L_0(z)                                            /
    
         + alpha^6 * (s(z*omega) * beta' + gamma' (beta' + 1))         \
                   * (z - omega^{n-1}) * z_lookup(z*omega)             | - lookup contribution
         - alpha^7 * L_0(z)                                            |
         - alpha^8 * L_{n-1}(z) * (gamma' (beta' + 1))^{n-1}           /
    
     In the end we should check that t(z)*Z_H(z) = r(z) + r_0! *)

  proc high (
      stateAlpha
      stateBeta
      stateBetaLookup
      stateGamma
      stateGammaLookup
      stateZ
      proofPublicInput
      proofCopyPermutationPolys0OpeningAtZ
      proofCopyPermutationPolys1OpeningAtZ
      proofCopyPermutationPolys2OpeningAtZ
      proofStatePolys0OpeningAtZ
      proofStatePolys1OpeningAtZ
      proofStatePolys2OpeningAtZ
      proofStatePolys3OpeningAtZ
      proofLookupSPolyOpeningAtZOmega
      proofLookupGrandProductOpeningAtZOmega
      proofGateSelectors0OpeningAtZ
      proofLinearisationPolyOpeningAtZ
      proofCopyPermutationGrandProductOpeningAtZOmega
      stateZInDomainSize
      proofQuotientPolyOpeningAtZ : FieldR.F) :
  (bool option * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F * FieldR.F) = {
    var r;
    var stateL0AtZ, stateLnMinusOneAtZ : FieldR.F;

    if (stateZ^Constants.DOMAIN_SIZE = FieldR.one) {
      r <- None;
      stateL0AtZ <- FieldR.zero;
      stateLnMinusOneAtZ <- FieldR.zero;
    } else {
      stateL0AtZ <- (stateZ^Constants.DOMAIN_SIZE - FieldR.one) * ((Constants.DOMAIN_SIZEFr * (stateZ - FieldR.one)) ^ (- 1));
      stateLnMinusOneAtZ <- (Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1) * (stateZ^Constants.DOMAIN_SIZE - FieldR.one)) * ((Constants.DOMAIN_SIZEFr * (stateZ - Constants.OMEGAFr^(Constants.DOMAIN_SIZE- 1))) ^ (- 1)); 

      r <- Some ((proofQuotientPolyOpeningAtZ * (stateZInDomainSize - FieldR.one)) 
         = (proofLinearisationPolyOpeningAtZ + stateL0AtZ * proofPublicInput * proofGateSelectors0OpeningAtZ -stateAlpha^4 * proofCopyPermutationGrandProductOpeningAtZOmega 
         * (proofCopyPermutationPolys0OpeningAtZ * stateBeta + stateGamma + proofStatePolys0OpeningAtZ) 
         * (proofCopyPermutationPolys1OpeningAtZ * stateBeta + stateGamma + proofStatePolys1OpeningAtZ) 
         * (proofCopyPermutationPolys2OpeningAtZ * stateBeta + stateGamma + proofStatePolys2OpeningAtZ) 
         * (proofStatePolys3OpeningAtZ + stateGamma)
      -stateAlpha^5 * stateL0AtZ  + ((stateAlpha^6 * (proofLookupSPolyOpeningAtZOmega * stateBetaLookup + stateGammaLookup * (stateBetaLookup + FieldR.one)) * proofLookupGrandProductOpeningAtZOmega) * (stateZ - Constants.OMEGAFr ^(Constants.DOMAIN_SIZE - 1)) 
        - stateAlpha^7 * stateL0AtZ 
        - stateAlpha^8 * stateLnMinusOneAtZ * (stateGammaLookup * (stateBetaLookup + FieldR.one)) ^ (Constants.DOMAIN_SIZE - 1))));
    }
    
    return (r,
      stateAlpha^2,
      stateAlpha^3,
      stateAlpha^4,
      stateAlpha^5,
      stateAlpha^6, 
      stateAlpha^7,
      stateAlpha^8,
      stateL0AtZ,
      stateLnMinusOneAtZ,
      stateBetaLookup + FieldR.one,
      stateGammaLookup * stateBetaLookup + stateGammaLookup,
      stateZ - Constants.OMEGAFr ^(Constants.DOMAIN_SIZE - 1)
    );
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

import MemoryMap PurePrimops.

lemma verifyQuotientEvaluation_low_pspec_revert:
    phoare [
      VerifyQuotientEvaluation.low:
      Primops.reverted ==> Primops.reverted
    ] = 1%r.
    proof.
      proc.
      inline RevertWithMessage.low Primops.revert Primops.mstore.
      wp.
      do 3! (call ConcretePrimops.mload_pspec_revert; wp).
      call lookupQuotientContribution_pspec_revert. wp.
      call permutationQuotientContribution_pspec_revert. wp.
      do 3! (call ConcretePrimops.mload_pspec_revert; wp).
      call evaluateLagrangePolyOutOfDomain_pspec_revert. wp.
      call evaluateLagrangePolyOutOfDomain_pspec_revert.      
      call ConcretePrimops.mload_pspec_revert. wp.
      call ConcretePrimops.mload_pspec_revert. skip.
      by progress.
qed.

op verifyQuotientEvaluation_memory_footprint (m: mem)
(a2 a3 a4 a5 a6 a7 a8 : uint256)
(sl0az slnm1az : uint256)
(bpo bgpg zmlo : uint256)
(v1 v2 v3 v4 v5 v6 v7 v8 : uint256) =
let m2 = store m  STATE_POWER_OF_ALPHA_2_SLOT a2 in
let m3 = store m2 STATE_POWER_OF_ALPHA_3_SLOT a3 in
let m4 = store m3 STATE_POWER_OF_ALPHA_4_SLOT a4 in
let m5 = store m4 STATE_POWER_OF_ALPHA_5_SLOT a5 in
let m6 = store m5 STATE_POWER_OF_ALPHA_6_SLOT a6 in
let m7 = store m6 STATE_POWER_OF_ALPHA_7_SLOT a7 in
let m8 = store m7 STATE_POWER_OF_ALPHA_8_SLOT a8 in
let m9 = lagrange_memory_footprint m8 v1 v2 v3 in
let m10 = store m9 STATE_L_0_AT_Z_SLOT sl0az in
let m11 = lagrange_memory_footprint m10 v4 v5 v6 in
let m12 = store m11 STATE_L_N_MINUS_ONE_AT_Z_SLOT slnm1az in
let m13 = lookupQuotientContribution_memory_footprint m12 v7 bpo bgpg zmlo v8 in
m13.

lemma verifyQuotientEvaluation_low_equiv_mid (m : mem) (
      stateAlphaG
      stateBetaG
      stateBetaLookupG
      stateGammaG
      stateGammaLookupG
      stateZG
      proofPublicInputG
      proofCopyPermutationPolys0OpeningAtZG
      proofCopyPermutationPolys1OpeningAtZG
      proofCopyPermutationPolys2OpeningAtZG
      proofStatePolys0OpeningAtZG
      proofStatePolys1OpeningAtZG
      proofStatePolys2OpeningAtZG
      proofStatePolys3OpeningAtZG
      proofLookupSPolyOpeningAtZOmegaG
      proofLookupGrandProductOpeningAtZOmegaG
      proofGateSelectors0OpeningAtZG
      proofLinearisationPolyOpeningAtZG
      proofCopyPermutationGrandProductOpeningAtZOmegaG
      stateZInDomainSizeG
      proofQuotientPolyOpeningAtZG
) :
equiv [VerifyQuotientEvaluation.low ~ VerifyQuotientEvaluation.mid :
arg{2} =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG, stateZG,
   proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG, proofCopyPermutationPolys2OpeningAtZG,
   proofStatePolys0OpeningAtZG, proofStatePolys1OpeningAtZG,
   proofStatePolys2OpeningAtZG, proofStatePolys3OpeningAtZG,
   proofLookupSPolyOpeningAtZOmegaG, proofLookupGrandProductOpeningAtZOmegaG,
   proofGateSelectors0OpeningAtZG, proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
   proofQuotientPolyOpeningAtZG) /\
Primops.memory{1} = m /\
!Primops.reverted{1} /\  
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG
==>
((((stateZG^Constants.DOMAIN_SIZE) - 1) %% Constants.R = 0 /\ res{2}.`1 = None /\ Primops.reverted{1})
 \/
 (((stateZG^Constants.DOMAIN_SIZE) - 1) %% Constants.R <> 0 /\ res{2}.`1 = Some false /\ Primops.reverted{1}))
\/
(!Primops.reverted{1} /\
  ((stateZG^Constants.DOMAIN_SIZE) - 1) %% Constants.R <> 0 /\
  exists (v1 v2 v3 v4 v5 v6 v7 v8 : uint256),
  Primops.memory{1} = verifyQuotientEvaluation_memory_footprint m 
  (W256.of_int res{2}.`2) (W256.of_int res{2}.`3) (W256.of_int res{2}.`4) (W256.of_int res{2}.`5) 
  (W256.of_int res{2}.`6) (W256.of_int res{2}.`7) (W256.of_int res{2}.`8)
  (W256.of_int res{2}.`9) (W256.of_int res{2}.`10)
  (W256.of_int res{2}.`11) (W256.of_int res{2}.`12) (W256.of_int res{2}.`13)
  v1 v2 v3 v4 v5 v6 v7 v8 /\
  res{2}.`1 = Some true /\
  0 <= res{2}.`2 < Constants.R /\
  0 <= res{2}.`3 < Constants.R /\
  0 <= res{2}.`4 < Constants.R /\
  0 <= res{2}.`5 < Constants.R /\
  0 <= res{2}.`6 < Constants.R /\
  0 <= res{2}.`7 < Constants.R /\
  0 <= res{2}.`8 < Constants.R /\
  0 <= res{2}.`9 < Constants.R /\
  0 <= res{2}.`10 < Constants.R /\
  0 <= res{2}.`11 < Constants.R /\
  0 <= res{2}.`12 < Constants.R /\
  0 <= res{2}.`13 < Constants.R)
].
proof. proc.

seq 1 0: (#pre /\ to_uint alpha{1} = stateAlpha{2}).
call{1} (ConcretePrimops.mload_pspec m STATE_ALPHA_SLOT). skip. by progress. 

seq 1 1: (#pre /\ to_uint currentAlpha{1} = statePowerOfAlpha2{2} /\ statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R).
wp. skip. rewrite /mulmod. progress. rewrite H0. smt(@W256 @Utils).
exists* statePowerOfAlpha2{2}. elim*=> a2.
pose m2 := store m STATE_POWER_OF_ALPHA_2_SLOT (W256.of_int a2).
seq 1 0: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
    !Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    to_uint currentAlpha{1} = statePowerOfAlpha2{2} /\
    a2 = statePowerOfAlpha2{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    Primops.memory{1} = m2
).
call{1} (ConcretePrimops.mstore_pspec m STATE_POWER_OF_ALPHA_2_SLOT (W256.of_int a2)).
skip. by progress.

seq 1 1: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
Primops.memory{1} = store m STATE_POWER_OF_ALPHA_2_SLOT (W256.of_int statePowerOfAlpha2{2}) /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha3{2} /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R
).
wp. skip. rewrite /mulmod. progress. rewrite H1 -H0.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils). 
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). rewrite H1 -H0. smt().
exists* statePowerOfAlpha3{2}. elim*=> a3.
pose m3 := store m2 STATE_POWER_OF_ALPHA_3_SLOT (W256.of_int a3).
seq 1 0: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha3{2} /\
    Primops.memory{1} = m3
).
call{1} (ConcretePrimops.mstore_pspec m2 STATE_POWER_OF_ALPHA_3_SLOT (W256.of_int a3)).
skip. by progress.

seq 1 1: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha4{2} = (statePowerOfAlpha3{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha4{2} /\
    Primops.memory{1} = m3
).
wp. skip. rewrite /mulmod. progress. smt(). rewrite H1 -H0.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils).
exists* statePowerOfAlpha4{2}. elim*=> a4.
pose m4 := store m3 STATE_POWER_OF_ALPHA_4_SLOT (W256.of_int a4).
seq 1 0: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    a4 = statePowerOfAlpha4{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha4{2} = (statePowerOfAlpha3{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha4{2} /\
    Primops.memory{1} = m4
).
call{1} (ConcretePrimops.mstore_pspec m3 STATE_POWER_OF_ALPHA_4_SLOT (W256.of_int a4)).
skip. progress. smt(@W256 @Utils).

seq 1 1: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    a4 = statePowerOfAlpha4{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha4{2} = (statePowerOfAlpha3{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha5{2} = (statePowerOfAlpha4{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha5{2} /\
    Primops.memory{1} = m4
).
wp. skip. rewrite /mulmod. progress. smt(). rewrite H1 -H0.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils).
exists* statePowerOfAlpha5{2}. elim*=> a5.
pose m5 := store m4 STATE_POWER_OF_ALPHA_5_SLOT (W256.of_int a5).
seq 1 0: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    a4 = statePowerOfAlpha4{2} /\
    a5 = statePowerOfAlpha5{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha4{2} = (statePowerOfAlpha3{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha5{2} = (statePowerOfAlpha4{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha5{2} /\
    Primops.memory{1} = m5
).
call{1} (ConcretePrimops.mstore_pspec m4 STATE_POWER_OF_ALPHA_5_SLOT (W256.of_int a5)).
skip. progress. smt(@W256 @Utils). 

seq 1 1: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    a4 = statePowerOfAlpha4{2} /\
    a5 = statePowerOfAlpha5{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha4{2} = (statePowerOfAlpha3{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha5{2} = (statePowerOfAlpha4{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha6{2} = (statePowerOfAlpha5{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha6{2} /\
    Primops.memory{1} = m5
).
wp. skip. rewrite /mulmod. progress. smt(). rewrite H1 -H0.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils).
exists* statePowerOfAlpha6{2}. elim*=> a6.
pose m6 := store m5 STATE_POWER_OF_ALPHA_6_SLOT (W256.of_int a6).
seq 1 0: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    a4 = statePowerOfAlpha4{2} /\
    a5 = statePowerOfAlpha5{2} /\
    a6 = statePowerOfAlpha6{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha4{2} = (statePowerOfAlpha3{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha5{2} = (statePowerOfAlpha4{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha6{2} = (statePowerOfAlpha5{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha6{2} /\
    Primops.memory{1} = m6
).
call{1} (ConcretePrimops.mstore_pspec m5 STATE_POWER_OF_ALPHA_6_SLOT (W256.of_int a6)).
skip. progress. smt(@W256 @Utils).

seq 1 1: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    a4 = statePowerOfAlpha4{2} /\
    a5 = statePowerOfAlpha5{2} /\
    a6 = statePowerOfAlpha6{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha4{2} = (statePowerOfAlpha3{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha5{2} = (statePowerOfAlpha4{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha6{2} = (statePowerOfAlpha5{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha7{2} = (statePowerOfAlpha6{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha7{2} /\
    Primops.memory{1} = m6
).
wp. skip. rewrite /mulmod. progress. smt(). rewrite H1 -H0.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils).
exists* statePowerOfAlpha7{2}. elim*=> a7.
pose m7 := store m6 STATE_POWER_OF_ALPHA_7_SLOT (W256.of_int a7).
seq 1 0: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    a4 = statePowerOfAlpha4{2} /\
    a5 = statePowerOfAlpha5{2} /\
    a6 = statePowerOfAlpha6{2} /\
    a7 = statePowerOfAlpha7{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha4{2} = (statePowerOfAlpha3{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha5{2} = (statePowerOfAlpha4{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha6{2} = (statePowerOfAlpha5{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha7{2} = (statePowerOfAlpha6{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha7{2} /\
    Primops.memory{1} = m7
).
call{1} (ConcretePrimops.mstore_pspec m6 STATE_POWER_OF_ALPHA_7_SLOT (W256.of_int a7)).
skip. progress. smt(@W256 @Utils).

seq 1 1: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    a4 = statePowerOfAlpha4{2} /\
    a5 = statePowerOfAlpha5{2} /\
    a6 = statePowerOfAlpha6{2} /\
    a7 = statePowerOfAlpha7{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha4{2} = (statePowerOfAlpha3{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha5{2} = (statePowerOfAlpha4{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha6{2} = (statePowerOfAlpha5{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha7{2} = (statePowerOfAlpha6{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha8{2} = (statePowerOfAlpha7{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha8{2} /\
    Primops.memory{1} = m7
).
wp. skip. rewrite /mulmod. progress. smt(). rewrite H1 -H0.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils).
rewrite W256.to_uint_small. progress. smt(@W256 @Utils).
exists* statePowerOfAlpha8{2}. elim*=> a8.
pose m8 := store m7 STATE_POWER_OF_ALPHA_8_SLOT (W256.of_int a8).
seq 1 0: (
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    to_uint alpha{1} = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    a4 = statePowerOfAlpha4{2} /\
    a5 = statePowerOfAlpha5{2} /\
    a6 = statePowerOfAlpha6{2} /\
    a7 = statePowerOfAlpha7{2} /\
    a8 = statePowerOfAlpha8{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha3{2} = (statePowerOfAlpha2{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha4{2} = (statePowerOfAlpha3{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha5{2} = (statePowerOfAlpha4{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha6{2} = (statePowerOfAlpha5{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha7{2} = (statePowerOfAlpha6{2} * stateAlpha{2}) %% Constants.R /\
    statePowerOfAlpha8{2} = (statePowerOfAlpha7{2} * stateAlpha{2}) %% Constants.R /\
    to_uint currentAlpha{1} = statePowerOfAlpha8{2} /\
    Primops.memory{1} = m8
).
call{1} (ConcretePrimops.mstore_pspec m7 STATE_POWER_OF_ALPHA_8_SLOT (W256.of_int a8)).
skip. progress. smt(@W256 @Utils).
exists* stateAlpha{2}; elim*=> a.
seq 0 0 :(
(stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
 stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
 proofCopyPermutationPolys0OpeningAtZ{2},
 proofCopyPermutationPolys1OpeningAtZ{2},
 proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
 proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
 proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
 proofLookupGrandProductOpeningAtZOmega{2},
 proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
 proofCopyPermutationGrandProductOpeningAtZOmega{2},
 stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
(stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
 stateGammaLookupG, stateZG, proofPublicInputG,
 proofCopyPermutationPolys0OpeningAtZG,
 proofCopyPermutationPolys1OpeningAtZG,
 proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
 proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
 proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
 proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
 proofLinearisationPolyOpeningAtZG,
 proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
 proofQuotientPolyOpeningAtZG) /\
W256.to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
W256.to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = proofCopyPermutationPolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = proofStatePolys0OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = proofStatePolys1OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = proofStatePolys2OpeningAtZG /\
W256.to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = proofStatePolys3OpeningAtZG /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = proofGateSelectors0OpeningAtZG /\
W256.to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = proofLinearisationPolyOpeningAtZG /\
W256.to_uint (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofCopyPermutationGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
W256.to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = proofQuotientPolyOpeningAtZG /\
!Primops.reverted{1} /\
    a = stateAlpha{2} /\
    a2 = statePowerOfAlpha2{2} /\
    a3 = statePowerOfAlpha3{2} /\
    a4 = statePowerOfAlpha4{2} /\
    a5 = statePowerOfAlpha5{2} /\
    a6 = statePowerOfAlpha6{2} /\
    a7 = statePowerOfAlpha7{2} /\
    a8 = statePowerOfAlpha8{2} /\
    statePowerOfAlpha2{2} = (stateAlpha{2}^2) %% Constants.R /\
    statePowerOfAlpha3{2} = (stateAlpha{2}^3) %% Constants.R /\
    statePowerOfAlpha4{2} = (stateAlpha{2}^4) %% Constants.R /\
    statePowerOfAlpha5{2} = (stateAlpha{2}^5) %% Constants.R /\
    statePowerOfAlpha6{2} = (stateAlpha{2}^6) %% Constants.R /\
    statePowerOfAlpha7{2} = (stateAlpha{2}^7) %% Constants.R /\
    statePowerOfAlpha8{2} = (stateAlpha{2}^8) %% Constants.R /\
    Primops.memory{1} = m8
).
skip; progress; smt().

seq 1 0 :(#pre /\ to_uint stateZ{1} = stateZ{2}).
call{1} (ConcretePrimops.mload_pspec m8 STATE_Z_SLOT).
skip; progress; rewrite /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1. 
do 7! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
; try by progress).

seq 1 1: (
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
    stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
    proofCopyPermutationPolys0OpeningAtZ{2},
    proofCopyPermutationPolys1OpeningAtZ{2},
    proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
    proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
    proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
    proofLookupGrandProductOpeningAtZOmega{2},
    proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
    proofCopyPermutationGrandProductOpeningAtZOmega{2},
    stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
   (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
    stateGammaLookupG, stateZG, proofPublicInputG,
    proofCopyPermutationPolys0OpeningAtZG,
    proofCopyPermutationPolys1OpeningAtZG,
    proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
    proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
    proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
    proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
    proofLinearisationPolyOpeningAtZG,
    proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG) /\
   to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
   to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
   to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
   to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
   to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
   to_uint (mload m STATE_Z_SLOT) = stateZG /\
   to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys0OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys1OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
   proofStatePolys0OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
   proofStatePolys1OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
   proofStatePolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
   proofStatePolys3OpeningAtZG /\
   to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupSPolyOpeningAtZOmegaG /\
   to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupGrandProductOpeningAtZOmegaG /\
   to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
   proofGateSelectors0OpeningAtZG /\
   to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
   proofLinearisationPolyOpeningAtZG /\
   to_uint
     (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofCopyPermutationGrandProductOpeningAtZOmegaG /\
   to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
   to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
   proofQuotientPolyOpeningAtZG /\
   a = stateAlpha{2} /\
   a2 = statePowerOfAlpha2{2} /\
   a3 = statePowerOfAlpha3{2} /\
   a4 = statePowerOfAlpha4{2} /\
   a5 = statePowerOfAlpha5{2} /\
   a6 = statePowerOfAlpha6{2} /\
   a7 = statePowerOfAlpha7{2} /\
   a8 = statePowerOfAlpha8{2} /\
   statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
   statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
   statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
   statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
   statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
   statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
   statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
   to_uint stateZ{1} = stateZ{2} /\
   ((!Primops.reverted{1} /\ ((stateZ{2}^Constants.DOMAIN_SIZE) - 1) %% Constants.R <> 0 /\
      exists v1 v2 v3, Primops.memory{1} = lagrange_memory_footprint m8 v1 v2 v3 /\
      elpodL0{2} = Some (W256.to_uint _12{1}) /\ 0 <= (W256.to_uint _12{1}) < Constants.R)
      \/
    (Primops.reverted{1} /\ ((stateZ{2}^Constants.DOMAIN_SIZE) - 1) %% Constants.R = 0 /\
      elpodL0{2} = None)) 
).
call (evaluateLagrangePolyOutOfDomain_low_equiv_mid m8 W256.zero (W256.of_int stateZG)).
skip. progress. smt(@W256). 

(* First evaluateLagrangePolyOutOfDomain REVERT *)
case (Primops.reverted{1}).
seq 0 0: (stateZ{2} = stateZG /\ Primops.reverted{1} /\ ((stateZ{2}^Constants.DOMAIN_SIZE) - 1) %% Constants.R = 0 /\ elpodL0{2} = None).
skip; progress; case H0; by progress.
rcondt{2} 1. by progress.
seq 1 1: (#pre /\ r{2} = None).
wp. call{1} (ConcretePrimops.mstore_pspec_revert). skip. by progress.
seq 1 0 : (#pre). call{1} (evaluateLagrangePolyOutOfDomain_pspec_revert); skip; by progress.
seq 1 0 : (#pre). call{1} (ConcretePrimops.mstore_pspec_revert); skip; by progress.
seq 1 0 : (#pre). call{1} (ConcretePrimops.mload_pspec_revert); skip; by progress.
seq 1 0 : (#pre). call{1} (ConcretePrimops.mload_pspec_revert); skip; by progress.
sp. seq 1 0 : (#pre). call{1} (ConcretePrimops.mload_pspec_revert); skip; by progress.
sp. seq 1 0 : (#pre). call{1} (permutationQuotientContribution_pspec_revert); skip; by progress.
sp. seq 1 0 : (#pre). call{1} (lookupQuotientContribution_pspec_revert); skip. progress. smt().
sp. seq 1 0 : (#pre). call{1} (ConcretePrimops.mload_pspec_revert); skip; smt().
sp. seq 1 0 : (#pre). call{1} (ConcretePrimops.mload_pspec_revert); skip; smt().
sp. seq 1 0 : (#pre). call{1} (ConcretePrimops.mload_pspec_revert); skip; smt().
sp. case (bool_of_uint256 (iszero (eq_uint256 lhs{1} result{1}))).
rcondt{1} 1. by progress.
call{1} (revertWithMessage_low_pspec). skip. by progress.
rcondf{1} 1. by progress. skip. by progress.

(* First evaluateLagrangePolyOutOfDomain NOT REVERT *)
elim*. progress. pose m9 := lagrange_memory_footprint m8 v1 v2 v3.
seq 0 0: (
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
    stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
    proofCopyPermutationPolys0OpeningAtZ{2},
    proofCopyPermutationPolys1OpeningAtZ{2},
    proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
    proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
    proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
    proofLookupGrandProductOpeningAtZOmega{2},
    proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
    proofCopyPermutationGrandProductOpeningAtZOmega{2},
    stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
   (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
    stateGammaLookupG, stateZG, proofPublicInputG,
    proofCopyPermutationPolys0OpeningAtZG,
    proofCopyPermutationPolys1OpeningAtZG,
    proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
    proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
    proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
    proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
    proofLinearisationPolyOpeningAtZG,
    proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG) /\
   to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
   to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
   to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
   to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
   to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
   to_uint (mload m STATE_Z_SLOT) = stateZG /\
   to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys0OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys1OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
   proofStatePolys0OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
   proofStatePolys1OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
   proofStatePolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
   proofStatePolys3OpeningAtZG /\
   to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupSPolyOpeningAtZOmegaG /\
   to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupGrandProductOpeningAtZOmegaG /\
   to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
   proofGateSelectors0OpeningAtZG /\
   to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
   proofLinearisationPolyOpeningAtZG /\
   to_uint
     (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofCopyPermutationGrandProductOpeningAtZOmegaG /\
   to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
   to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
   proofQuotientPolyOpeningAtZG /\
   a = stateAlpha{2} /\
   a2 = statePowerOfAlpha2{2} /\
   a3 = statePowerOfAlpha3{2} /\
   a4 = statePowerOfAlpha4{2} /\
   a5 = statePowerOfAlpha5{2} /\
   a6 = statePowerOfAlpha6{2} /\
   a7 = statePowerOfAlpha7{2} /\
   a8 = statePowerOfAlpha8{2} /\
   statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
   statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
   statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
   statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
   statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
   statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
   statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
   to_uint stateZ{1} = stateZ{2} /\
   (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
   elpodL0{2} = Some (to_uint _12{1}) /\
   0 <= to_uint _12{1} < Constants.R /\
   !Primops.reverted{1} /\
   Primops.memory{1} = m9
). skip; progress; smt().

rcondf{2} 1. by progress.
exists* _12{1}; elim*=> sl0az. pose m10 := store m9 STATE_L_0_AT_Z_SLOT sl0az.
seq 1 1: (
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
    stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
    proofCopyPermutationPolys0OpeningAtZ{2},
    proofCopyPermutationPolys1OpeningAtZ{2},
    proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
    proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
    proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
    proofLookupGrandProductOpeningAtZOmega{2},
    proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
    proofCopyPermutationGrandProductOpeningAtZOmega{2},
    stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
   (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
    stateGammaLookupG, stateZG, proofPublicInputG,
    proofCopyPermutationPolys0OpeningAtZG,
    proofCopyPermutationPolys1OpeningAtZG,
    proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
    proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
    proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
    proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
    proofLinearisationPolyOpeningAtZG,
    proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG) /\
   to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
   to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
   to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
   to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
   to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
   to_uint (mload m STATE_Z_SLOT) = stateZG /\
   to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys0OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys1OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
   proofStatePolys0OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
   proofStatePolys1OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
   proofStatePolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
   proofStatePolys3OpeningAtZG /\
   to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupSPolyOpeningAtZOmegaG /\
   to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupGrandProductOpeningAtZOmegaG /\
   to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
   proofGateSelectors0OpeningAtZG /\
   to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
   proofLinearisationPolyOpeningAtZG /\
   to_uint
     (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofCopyPermutationGrandProductOpeningAtZOmegaG /\
   to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
   to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
   proofQuotientPolyOpeningAtZG /\
   a = stateAlpha{2} /\
   a2 = statePowerOfAlpha2{2} /\
   a3 = statePowerOfAlpha3{2} /\
   a4 = statePowerOfAlpha4{2} /\
   a5 = statePowerOfAlpha5{2} /\
   a6 = statePowerOfAlpha6{2} /\
   a7 = statePowerOfAlpha7{2} /\
   a8 = statePowerOfAlpha8{2} /\
   statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
   statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
   statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
   statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
   statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
   statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
   statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
   sl0az = _12{1} /\ to_uint _12{1} = stateL0AtZ{2} /\
   to_uint stateZ{1} = stateZ{2} /\
   (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
   elpodL0{2} = Some (to_uint _12{1}) /\
   0 <= to_uint _12{1} < Constants.R /\
   !Primops.reverted{1} /\
   Primops.memory{1} = m10
). 
wp. call{1} (ConcretePrimops.mstore_pspec m9 STATE_L_0_AT_Z_SLOT sl0az).
skip. by progress.

seq 1 1: (
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
    stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
    proofCopyPermutationPolys0OpeningAtZ{2},
    proofCopyPermutationPolys1OpeningAtZ{2},
    proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
    proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
    proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
    proofLookupGrandProductOpeningAtZOmega{2},
    proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
    proofCopyPermutationGrandProductOpeningAtZOmega{2},
    stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
   (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
    stateGammaLookupG, stateZG, proofPublicInputG,
    proofCopyPermutationPolys0OpeningAtZG,
    proofCopyPermutationPolys1OpeningAtZG,
    proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
    proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
    proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
    proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
    proofLinearisationPolyOpeningAtZG,
    proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG) /\
   to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
   to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
   to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
   to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
   to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
   to_uint (mload m STATE_Z_SLOT) = stateZG /\
   to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys0OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys1OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
   proofStatePolys0OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
   proofStatePolys1OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
   proofStatePolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
   proofStatePolys3OpeningAtZG /\
   to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupSPolyOpeningAtZOmegaG /\
   to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupGrandProductOpeningAtZOmegaG /\
   to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
   proofGateSelectors0OpeningAtZG /\
   to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
   proofLinearisationPolyOpeningAtZG /\
   to_uint
     (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofCopyPermutationGrandProductOpeningAtZOmegaG /\
   to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
   to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
   proofQuotientPolyOpeningAtZG /\
   a = stateAlpha{2} /\
   a2 = statePowerOfAlpha2{2} /\
   a3 = statePowerOfAlpha3{2} /\
   a4 = statePowerOfAlpha4{2} /\
   a5 = statePowerOfAlpha5{2} /\
   a6 = statePowerOfAlpha6{2} /\
   a7 = statePowerOfAlpha7{2} /\
   a8 = statePowerOfAlpha8{2} /\
   statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
   statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
   statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
   statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
   statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
   statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
   statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
   sl0az = _12{1} /\ to_uint _12{1} = stateL0AtZ{2} /\
   to_uint stateZ{1} = stateZ{2} /\
   (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
   elpodL0{2} = Some (to_uint _12{1}) /\
   elpodLn{2} = Some (to_uint _17{1}) /\
   0 <= to_uint _12{1} < Constants.R /\
   0 <= to_uint _17{1} < Constants.R /\
   !Primops.reverted{1} /\
   exists v4 v5 v6, Primops.memory{1} = lagrange_memory_footprint m10 v4 v5 v6
).
call (evaluateLagrangePolyOutOfDomain_low_equiv_mid m10 (DOMAIN_SIZE - W256.one) (W256.of_int stateZG)).
skip. progress. smt(@W256). rewrite /DOMAIN_SIZE. smt(). smt(). smt(). smt(). smt(). smt().

rewrite /lagrange_memory_footprint. elim*. progress.
pose m11 := lagrange_memory_footprint m10 v4 v5 v6.
seq 0 0: (
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
    stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
    proofCopyPermutationPolys0OpeningAtZ{2},
    proofCopyPermutationPolys1OpeningAtZ{2},
    proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
    proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
    proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
    proofLookupGrandProductOpeningAtZOmega{2},
    proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
    proofCopyPermutationGrandProductOpeningAtZOmega{2},
    stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
   (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
    stateGammaLookupG, stateZG, proofPublicInputG,
    proofCopyPermutationPolys0OpeningAtZG,
    proofCopyPermutationPolys1OpeningAtZG,
    proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
    proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
    proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
    proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
    proofLinearisationPolyOpeningAtZG,
    proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG) /\
   to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
   to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
   to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
   to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
   to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
   to_uint (mload m STATE_Z_SLOT) = stateZG /\
   to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys0OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys1OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
   proofStatePolys0OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
   proofStatePolys1OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
   proofStatePolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
   proofStatePolys3OpeningAtZG /\
   to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupSPolyOpeningAtZOmegaG /\
   to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupGrandProductOpeningAtZOmegaG /\
   to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
   proofGateSelectors0OpeningAtZG /\
   to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
   proofLinearisationPolyOpeningAtZG /\
   to_uint
     (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofCopyPermutationGrandProductOpeningAtZOmegaG /\
   to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
   to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
   proofQuotientPolyOpeningAtZG /\
   a = stateAlpha{2} /\
   a2 = statePowerOfAlpha2{2} /\
   a3 = statePowerOfAlpha3{2} /\
   a4 = statePowerOfAlpha4{2} /\
   a5 = statePowerOfAlpha5{2} /\
   a6 = statePowerOfAlpha6{2} /\
   a7 = statePowerOfAlpha7{2} /\
   a8 = statePowerOfAlpha8{2} /\
   statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
   statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
   statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
   statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
   statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
   statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
   statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
   sl0az = _12{1} /\ to_uint _12{1} = stateL0AtZ{2} /\
   to_uint stateZ{1} = stateZ{2} /\
   (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
   elpodL0{2} = Some (to_uint _12{1}) /\
   elpodLn{2} = Some (to_uint _17{1}) /\
   0 <= to_uint _12{1} < Constants.R /\
   0 <= to_uint _17{1} < Constants.R /\
   !Primops.reverted{1} /\
   Primops.memory{1} = m11
). 
skip. by progress. 

exists* _17{1}; elim*=> slnm1az. pose m12 := store m11 STATE_L_N_MINUS_ONE_AT_Z_SLOT slnm1az.
seq 1 1: (
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
    stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
    proofCopyPermutationPolys0OpeningAtZ{2},
    proofCopyPermutationPolys1OpeningAtZ{2},
    proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
    proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
    proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
    proofLookupGrandProductOpeningAtZOmega{2},
    proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
    proofCopyPermutationGrandProductOpeningAtZOmega{2},
    stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
   (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
    stateGammaLookupG, stateZG, proofPublicInputG,
    proofCopyPermutationPolys0OpeningAtZG,
    proofCopyPermutationPolys1OpeningAtZG,
    proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
    proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
    proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
    proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
    proofLinearisationPolyOpeningAtZG,
    proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG) /\
   to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
   to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
   to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
   to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
   to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
   to_uint (mload m STATE_Z_SLOT) = stateZG /\
   to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys0OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys1OpeningAtZG /\
   to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
   proofCopyPermutationPolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
   proofStatePolys0OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
   proofStatePolys1OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
   proofStatePolys2OpeningAtZG /\
   to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
   proofStatePolys3OpeningAtZG /\
   to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupSPolyOpeningAtZOmegaG /\
   to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupGrandProductOpeningAtZOmegaG /\
   to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
   proofGateSelectors0OpeningAtZG /\
   to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
   proofLinearisationPolyOpeningAtZG /\
   to_uint
     (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofCopyPermutationGrandProductOpeningAtZOmegaG /\
   to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
   to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
   proofQuotientPolyOpeningAtZG /\
   a = stateAlpha{2} /\
   a2 = statePowerOfAlpha2{2} /\
   a3 = statePowerOfAlpha3{2} /\
   a4 = statePowerOfAlpha4{2} /\
   a5 = statePowerOfAlpha5{2} /\
   a6 = statePowerOfAlpha6{2} /\
   a7 = statePowerOfAlpha7{2} /\
   a8 = statePowerOfAlpha8{2} /\
   statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
   statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
   statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
   statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
   statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
   statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
   statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
   sl0az = _12{1} /\ to_uint _12{1} = stateL0AtZ{2} /\
   slnm1az = _17{1} /\ to_uint _17{1} = stateLnMinusOneAtZ{2} /\  
   to_uint stateZ{1} = stateZ{2} /\
   (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
   elpodL0{2} = Some (to_uint _12{1}) /\
   elpodLn{2} = Some (to_uint _17{1}) /\
   0 <= to_uint _12{1} < Constants.R /\
   0 <= to_uint _17{1} < Constants.R /\
   !Primops.reverted{1} /\
   Primops.memory{1} = m12
).
wp. call{1} (ConcretePrimops.mstore_pspec m11 STATE_L_N_MINUS_ONE_AT_Z_SLOT slnm1az).
skip. by progress.

seq 1 0: (#pre /\ to_uint _20{1} = proofPublicInput{2}).
call{1} (ConcretePrimops.mload_pspec m12 PROOF_PUBLIC_INPUT). skip. progress.
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT ; try by progress).

seq 1 0: (#pre /\ _21{1} = _12{1}).
call{1} (ConcretePrimops.mload_pspec m12 STATE_L_0_AT_Z_SLOT).
skip. progress. 
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 7! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT ; try by progress).
rewrite load_store_same; reflexivity.

seq 1 1: (#pre /\
  to_uint stateT{1} = stateT{2} /\
  stateT{2} = (stateL0AtZ{2} * proofPublicInput{2}) %% Constants.R).
wp. skip. progress. rewrite /mulmod -H6. progress.
rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils). rewrite /R_MOD. smt().

seq 1 0: (#pre /\ to_uint _23{1} = proofGateSelectors0OpeningAtZ{2}).
call{1} (ConcretePrimops.mload_pspec m12 PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT).
skip. progress. 
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 23! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT ; try by progress).

seq 1 1: (#pre /\
  to_uint result{1} = pgsT{2} /\
  pgsT{2} = (stateT{2} * proofGateSelectors0OpeningAtZ{2}) %% Constants.R).
wp. skip. progress. rewrite /mulmod -H8. progress.
rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils). rewrite /R_MOD. smt().

seq 1 1: (#pre /\ to_uint _24{1} = pqc{2} /\ 0 <= pqc{2} < Constants.R).
call (permutationQuotientContribution_low_equiv_mid m12
      a4 a5
      proofCopyPermutationGrandProductOpeningAtZOmegaG
      stateBetaG
      stateGammaG
      proofCopyPermutationPolys0OpeningAtZG
      proofCopyPermutationPolys1OpeningAtZG
      proofCopyPermutationPolys2OpeningAtZG
      proofStatePolys0OpeningAtZG
      proofStatePolys1OpeningAtZG
      proofStatePolys2OpeningAtZG
      proofStatePolys3OpeningAtZG
      (W256.to_uint sl0az)).
skip. progress.
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 18! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT ; try by progress).
rewrite load_store_same; smt(@W256 @Utils).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 17! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT ; try by progress).
rewrite load_store_same; smt(@W256 @Utils).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_GAMMA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 7! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite load_store_same; reflexivity.

seq 1 1: (
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
         stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
         proofCopyPermutationPolys0OpeningAtZ{2},
         proofCopyPermutationPolys1OpeningAtZ{2},
         proofCopyPermutationPolys2OpeningAtZ{2},
         proofStatePolys0OpeningAtZ{2}, proofStatePolys1OpeningAtZ{2},
         proofStatePolys2OpeningAtZ{2}, proofStatePolys3OpeningAtZ{2},
         proofLookupSPolyOpeningAtZOmega{2},
         proofLookupGrandProductOpeningAtZOmega{2},
         proofGateSelectors0OpeningAtZ{2},
         proofLinearisationPolyOpeningAtZ{2},
         proofCopyPermutationGrandProductOpeningAtZOmega{2},
         stateZInDomainSize{2}, proofQuotientPolyOpeningAtZ{2}) =
        (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG,
         stateGammaLookupG, stateZG, proofPublicInputG,
         proofCopyPermutationPolys0OpeningAtZG,
         proofCopyPermutationPolys1OpeningAtZG,
         proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
         proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
         proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
         proofLookupGrandProductOpeningAtZOmegaG,
         proofGateSelectors0OpeningAtZG, proofLinearisationPolyOpeningAtZG,
         proofCopyPermutationGrandProductOpeningAtZOmegaG,
         stateZInDomainSizeG, proofQuotientPolyOpeningAtZG) /\
        to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
        to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
        to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
        to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
        to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
        to_uint (mload m STATE_Z_SLOT) = stateZG /\
        to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
        to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
        proofCopyPermutationPolys0OpeningAtZG /\
        to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
        proofCopyPermutationPolys1OpeningAtZG /\
        to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
        proofCopyPermutationPolys2OpeningAtZG /\
        to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
        proofStatePolys0OpeningAtZG /\
        to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
        proofStatePolys1OpeningAtZG /\
        to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
        proofStatePolys2OpeningAtZG /\
        to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
        proofStatePolys3OpeningAtZG /\
        to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
        proofLookupSPolyOpeningAtZOmegaG /\
        to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
        proofLookupGrandProductOpeningAtZOmegaG /\
        to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
        proofGateSelectors0OpeningAtZG /\
        to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
        proofLinearisationPolyOpeningAtZG /\
        to_uint
          (mload m
             PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
        proofCopyPermutationGrandProductOpeningAtZOmegaG /\
        to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
        to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
        proofQuotientPolyOpeningAtZG /\
        a = stateAlpha{2} /\
        a2 = statePowerOfAlpha2{2} /\
        a3 = statePowerOfAlpha3{2} /\
        a4 = statePowerOfAlpha4{2} /\
        a5 = statePowerOfAlpha5{2} /\
        a6 = statePowerOfAlpha6{2} /\
        a7 = statePowerOfAlpha7{2} /\
        a8 = statePowerOfAlpha8{2} /\
        statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
        statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
        statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
        statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
        statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
        statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
        statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
        sl0az = _12{1} /\
        to_uint _12{1} = stateL0AtZ{2} /\
        slnm1az = _17{1} /\
        to_uint _17{1} = stateLnMinusOneAtZ{2} /\
        to_uint stateZ{1} = stateZ{2} /\
        (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
        elpodL0{2} = Some (to_uint _12{1}) /\
        elpodLn{2} = Some (to_uint _17{1}) /\
        (0 <= to_uint _12{1} && to_uint _12{1} < Constants.R) /\
        (0 <= to_uint _17{1} && to_uint _17{1} < Constants.R) /\
        !Primops.reverted{1} /\ Primops.memory{1} = m12 /\
       to_uint _20{1} = proofPublicInput{2} /\
      _21{1} = _12{1} /\
     to_uint stateT{1} = stateT{2} /\
     stateT{2} = stateL0AtZ{2} * proofPublicInput{2} %% Constants.R /\
    to_uint _23{1} = proofGateSelectors0OpeningAtZ{2} /\
   pgsT{2} = stateT{2} * proofGateSelectors0OpeningAtZ{2} %% Constants.R /\
  to_uint _24{1} = pqc{2} /\ 0 <= pqc{2} && pqc{2} < Constants.R /\
  to_uint result{1} = pqcR{2} /\ pqcR{2} = (pgsT{2} + pqc{2}) %% Constants.R).
wp. skip. progress. rewrite /addmod. progress. 
rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils). rewrite /R_MOD. smt().

seq 1 1:(
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
   stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
   proofCopyPermutationPolys0OpeningAtZ{2},
   proofCopyPermutationPolys1OpeningAtZ{2},
   proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
   proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
   proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
   proofLookupGrandProductOpeningAtZOmega{2},
   proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
   proofCopyPermutationGrandProductOpeningAtZOmega{2}, stateZInDomainSize{2},
   proofQuotientPolyOpeningAtZ{2}) =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG,
   stateZG, proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG,
   proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
   proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
   proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
   proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
   proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
   proofQuotientPolyOpeningAtZG) /\
  to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
  to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
  to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
  to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
  to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
  to_uint (mload m STATE_Z_SLOT) = stateZG /\
  to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys0OpeningAtZG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys1OpeningAtZG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys2OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
  proofStatePolys0OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
  proofStatePolys1OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
  proofStatePolys2OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
  proofStatePolys3OpeningAtZG /\
  to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupSPolyOpeningAtZOmegaG /\
  to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupGrandProductOpeningAtZOmegaG /\
  to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
  proofGateSelectors0OpeningAtZG /\
  to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
  proofLinearisationPolyOpeningAtZG /\
  to_uint
    (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofCopyPermutationGrandProductOpeningAtZOmegaG /\
  to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
  to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
  proofQuotientPolyOpeningAtZG /\
  a = stateAlpha{2} /\
  a2 = statePowerOfAlpha2{2} /\
  a3 = statePowerOfAlpha3{2} /\
  a4 = statePowerOfAlpha4{2} /\
  a5 = statePowerOfAlpha5{2} /\
  a6 = statePowerOfAlpha6{2} /\
  a7 = statePowerOfAlpha7{2} /\
  a8 = statePowerOfAlpha8{2} /\
  statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
  statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
  statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
  statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
  statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
  statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
  statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
  sl0az = _12{1} /\
  to_uint _12{1} = stateL0AtZ{2} /\
  slnm1az = _17{1} /\
  to_uint _17{1} = stateLnMinusOneAtZ{2} /\
  to_uint stateZ{1} = stateZ{2} /\
  (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
  elpodL0{2} = Some (to_uint _12{1}) /\
  elpodLn{2} = Some (to_uint _17{1}) /\
  (0 <= to_uint _12{1} && to_uint _12{1} < Constants.R) /\
  (0 <= to_uint _17{1} && to_uint _17{1} < Constants.R) /\
  !Primops.reverted{1} /\
  to_uint _20{1} = proofPublicInput{2} /\
  _21{1} = _12{1} /\
  to_uint stateT{1} = stateT{2} /\
  stateT{2} = stateL0AtZ{2} * proofPublicInput{2} %% Constants.R /\
  to_uint _23{1} = proofGateSelectors0OpeningAtZ{2} /\
  pgsT{2} = stateT{2} * proofGateSelectors0OpeningAtZ{2} %% Constants.R /\
  to_uint _24{1} = pqc{2} /\
  0 <= pqc{2} &&
  pqc{2} < Constants.R /\
  to_uint result{1} = pqcR{2} /\ pqcR{2} = (pgsT{2} + pqc{2}) %% Constants.R /\
  to_uint _25{1} = lqc{2} /\ 0 <= lqc{2} < Constants.R /\
  0 <= stateBetaPlusOne{2} < Constants.R /\
  0 <= stateBetaGammaPlusGamma{2} < Constants.R /\
  0 <= stateZMinusLastOmega{2} < Constants.R /\
  exists v7 v8, Primops.memory{1} = lookupQuotientContribution_memory_footprint m12 v7 (W256.of_int stateBetaPlusOne{2}) (W256.of_int stateBetaGammaPlusGamma{2}) (W256.of_int stateZMinusLastOmega{2}) v8
).
call (lookupQuotientContribution_low_equiv_mid m12
        stateBetaLookupG stateGammaLookupG
        a6 a7 a8
        proofLookupSPolyOpeningAtZOmegaG
        proofLookupGrandProductOpeningAtZOmegaG
        stateZG
        (W256.to_uint sl0az) (W256.to_uint slnm1az)).
skip. progress.
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 16! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite load_store_same. smt(@W256 @Utils).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 15! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite load_store_same. smt(@W256 @Utils).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 14! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite load_store_same. smt(@W256 @Utils).

rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).

rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 22! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 7! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT ; try by progress).
rewrite load_store_same. reflexivity.
rewrite /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lagrange_memory_footprint /modexp_memory_footprint; progress.
rewrite load_store_same. reflexivity. smt().
exists (of_int v10)%W256 (of_int v20)%W256. reflexivity.

seq 0 0:(
  exists (v7 v8 : uint256),
    Primops.memory{1} =
    lookupQuotientContribution_memory_footprint m12 v7 (W256.of_int stateBetaPlusOne{2})
      (W256.of_int stateBetaGammaPlusGamma{2}) (W256.of_int stateZMinusLastOmega{2}) v8 /\        
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
   stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
   proofCopyPermutationPolys0OpeningAtZ{2},
   proofCopyPermutationPolys1OpeningAtZ{2},
   proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
   proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
   proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
   proofLookupGrandProductOpeningAtZOmega{2},
   proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
   proofCopyPermutationGrandProductOpeningAtZOmega{2}, stateZInDomainSize{2},
   proofQuotientPolyOpeningAtZ{2}) =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG,
   stateZG, proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG,
   proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
   proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
   proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
   proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
   proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
   proofQuotientPolyOpeningAtZG) /\
  to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
  to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
  to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
  to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
  to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
  to_uint (mload m STATE_Z_SLOT) = stateZG /\
  to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys0OpeningAtZG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys1OpeningAtZG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys2OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
  proofStatePolys0OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
  proofStatePolys1OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
  proofStatePolys2OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
  proofStatePolys3OpeningAtZG /\
  to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupSPolyOpeningAtZOmegaG /\
  to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupGrandProductOpeningAtZOmegaG /\
  to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
  proofGateSelectors0OpeningAtZG /\
  to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
  proofLinearisationPolyOpeningAtZG /\
  to_uint
    (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofCopyPermutationGrandProductOpeningAtZOmegaG /\
  to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
  to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
  proofQuotientPolyOpeningAtZG /\
  a = stateAlpha{2} /\
  a2 = statePowerOfAlpha2{2} /\
  a3 = statePowerOfAlpha3{2} /\
  a4 = statePowerOfAlpha4{2} /\
  a5 = statePowerOfAlpha5{2} /\
  a6 = statePowerOfAlpha6{2} /\
  a7 = statePowerOfAlpha7{2} /\
  a8 = statePowerOfAlpha8{2} /\
  statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
  statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
  statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
  statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
  statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
  statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
  statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
  sl0az = _12{1} /\
  to_uint _12{1} = stateL0AtZ{2} /\
  slnm1az = _17{1} /\
  to_uint _17{1} = stateLnMinusOneAtZ{2} /\
  to_uint stateZ{1} = stateZ{2} /\
  (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
  elpodL0{2} = Some (to_uint _12{1}) /\
  elpodLn{2} = Some (to_uint _17{1}) /\
  (0 <= to_uint _12{1} && to_uint _12{1} < Constants.R) /\
  (0 <= to_uint _17{1} && to_uint _17{1} < Constants.R) /\
  !Primops.reverted{1} /\
  to_uint _20{1} = proofPublicInput{2} /\
  _21{1} = _12{1} /\
  to_uint stateT{1} = stateT{2} /\
  stateT{2} = stateL0AtZ{2} * proofPublicInput{2} %% Constants.R /\
  to_uint _23{1} = proofGateSelectors0OpeningAtZ{2} /\
  pgsT{2} = stateT{2} * proofGateSelectors0OpeningAtZ{2} %% Constants.R /\
  to_uint _24{1} = pqc{2} /\
  0 <= pqc{2} &&
  pqc{2} < Constants.R /\
  to_uint result{1} = pqcR{2} /\
  pqcR{2} = (pgsT{2} + pqc{2}) %% Constants.R /\
  to_uint _25{1} = lqc{2} /\
  (0 <= lqc{2} && lqc{2} < Constants.R) /\
  (0 <= stateBetaPlusOne{2} && stateBetaPlusOne{2} < Constants.R) /\
  (0 <= stateBetaGammaPlusGamma{2} &&
   stateBetaGammaPlusGamma{2} < Constants.R) /\
  (0 <= stateZMinusLastOmega{2} && stateZMinusLastOmega{2} < Constants.R)
).
skip. progress. exists v7 v8. progress. elim*. progress.
exists* stateBetaPlusOne{2}, stateBetaGammaPlusGamma{2}, stateZMinusLastOmega{2}.
elim*=> sbpo sbgpg szmlo.
pose m13 := lookupQuotientContribution_memory_footprint m12 v7 (W256.of_int sbpo) (W256.of_int sbgpg) (W256.of_int szmlo) v8.

seq 0 0:(
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
   stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
   proofCopyPermutationPolys0OpeningAtZ{2},
   proofCopyPermutationPolys1OpeningAtZ{2},
   proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
   proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
   proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
   proofLookupGrandProductOpeningAtZOmega{2},
   proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
   proofCopyPermutationGrandProductOpeningAtZOmega{2}, stateZInDomainSize{2},
   proofQuotientPolyOpeningAtZ{2}) =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG,
   stateZG, proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG,
   proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
   proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
   proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
   proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
   proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
   proofQuotientPolyOpeningAtZG) /\
  to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
  to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
  to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
  to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
  to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
  to_uint (mload m STATE_Z_SLOT) = stateZG /\
  to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys0OpeningAtZG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys1OpeningAtZG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys2OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
  proofStatePolys0OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
  proofStatePolys1OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
  proofStatePolys2OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
  proofStatePolys3OpeningAtZG /\
  to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupSPolyOpeningAtZOmegaG /\
  to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupGrandProductOpeningAtZOmegaG /\
  to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
  proofGateSelectors0OpeningAtZG /\
  to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
  proofLinearisationPolyOpeningAtZG /\
  to_uint
    (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofCopyPermutationGrandProductOpeningAtZOmegaG /\
  to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
  to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
  proofQuotientPolyOpeningAtZG /\
  a = stateAlpha{2} /\
  a2 = statePowerOfAlpha2{2} /\
  a3 = statePowerOfAlpha3{2} /\
  a4 = statePowerOfAlpha4{2} /\
  a5 = statePowerOfAlpha5{2} /\
  a6 = statePowerOfAlpha6{2} /\
  a7 = statePowerOfAlpha7{2} /\
  a8 = statePowerOfAlpha8{2} /\
  statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
  statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
  statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
  statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
  statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
  statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
  statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
  sbpo = stateBetaPlusOne{2} /\
  sbgpg = stateBetaGammaPlusGamma{2} /\
  szmlo = stateZMinusLastOmega{2} /\  
  sl0az = _12{1} /\
  to_uint _12{1} = stateL0AtZ{2} /\
  slnm1az = _17{1} /\
  to_uint _17{1} = stateLnMinusOneAtZ{2} /\
  to_uint stateZ{1} = stateZ{2} /\
  (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
  elpodL0{2} = Some (to_uint _12{1}) /\
  elpodLn{2} = Some (to_uint _17{1}) /\
  (0 <= to_uint _12{1} && to_uint _12{1} < Constants.R) /\
  (0 <= to_uint _17{1} && to_uint _17{1} < Constants.R) /\
  !Primops.reverted{1} /\
  to_uint _20{1} = proofPublicInput{2} /\
  _21{1} = _12{1} /\
  to_uint stateT{1} = stateT{2} /\
  stateT{2} = stateL0AtZ{2} * proofPublicInput{2} %% Constants.R /\
  to_uint _23{1} = proofGateSelectors0OpeningAtZ{2} /\
  pgsT{2} = stateT{2} * proofGateSelectors0OpeningAtZ{2} %% Constants.R /\
  to_uint _24{1} = pqc{2} /\
  0 <= pqc{2} &&
  pqc{2} < Constants.R /\
  to_uint result{1} = pqcR{2} /\
  pqcR{2} = (pgsT{2} + pqc{2}) %% Constants.R /\
  to_uint _25{1} = lqc{2} /\
  (0 <= lqc{2} && lqc{2} < Constants.R) /\
  (0 <= stateBetaPlusOne{2} && stateBetaPlusOne{2} < Constants.R) /\
  (0 <= stateBetaGammaPlusGamma{2} &&
   stateBetaGammaPlusGamma{2} < Constants.R) /\
  (0 <= stateZMinusLastOmega{2} && stateZMinusLastOmega{2} < Constants.R) /\
  Primops.memory{1} = m13
).
skip. by progress. 

seq 2 1:(
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
   stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
   proofCopyPermutationPolys0OpeningAtZ{2},
   proofCopyPermutationPolys1OpeningAtZ{2},
   proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
   proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
   proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
   proofLookupGrandProductOpeningAtZOmega{2},
   proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
   proofCopyPermutationGrandProductOpeningAtZOmega{2}, stateZInDomainSize{2},
   proofQuotientPolyOpeningAtZ{2}) =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG,
   stateZG, proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG,
   proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
   proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
   proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
   proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
   proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
   proofQuotientPolyOpeningAtZG) /\
  to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
  to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
  to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
  to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
  to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
  to_uint (mload m STATE_Z_SLOT) = stateZG /\
  to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys0OpeningAtZG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys1OpeningAtZG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys2OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
  proofStatePolys0OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
  proofStatePolys1OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
  proofStatePolys2OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
  proofStatePolys3OpeningAtZG /\
  to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupSPolyOpeningAtZOmegaG /\
  to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupGrandProductOpeningAtZOmegaG /\
  to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
  proofGateSelectors0OpeningAtZG /\
  to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
  proofLinearisationPolyOpeningAtZG /\
  to_uint
    (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofCopyPermutationGrandProductOpeningAtZOmegaG /\
  to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
  to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
  proofQuotientPolyOpeningAtZG /\
  a = stateAlpha{2} /\
  a2 = statePowerOfAlpha2{2} /\
  a3 = statePowerOfAlpha3{2} /\
  a4 = statePowerOfAlpha4{2} /\
  a5 = statePowerOfAlpha5{2} /\
  a6 = statePowerOfAlpha6{2} /\
  a7 = statePowerOfAlpha7{2} /\
  a8 = statePowerOfAlpha8{2} /\
  statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
  statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
  statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
  statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
  statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
  statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
  statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
  sbpo = stateBetaPlusOne{2} /\
  sbgpg = stateBetaGammaPlusGamma{2} /\
  szmlo = stateZMinusLastOmega{2} /\
  sl0az = _12{1} /\
  to_uint _12{1} = stateL0AtZ{2} /\
  slnm1az = _17{1} /\
  to_uint _17{1} = stateLnMinusOneAtZ{2} /\
  to_uint stateZ{1} = stateZ{2} /\
  (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
  elpodL0{2} = Some (to_uint _12{1}) /\
  elpodLn{2} = Some (to_uint _17{1}) /\
  (0 <= to_uint _12{1} && to_uint _12{1} < Constants.R) /\
  (0 <= to_uint _17{1} && to_uint _17{1} < Constants.R) /\
  !Primops.reverted{1} /\
  to_uint _20{1} = proofPublicInput{2} /\
  _21{1} = _12{1} /\
  to_uint stateT{1} = stateT{2} /\
  stateT{2} = stateL0AtZ{2} * proofPublicInput{2} %% Constants.R /\
  to_uint _23{1} = proofGateSelectors0OpeningAtZ{2} /\
  pgsT{2} = stateT{2} * proofGateSelectors0OpeningAtZ{2} %% Constants.R /\
  to_uint _24{1} = pqc{2} /\
  0 <= pqc{2} &&
  pqc{2} < Constants.R /\
  pqcR{2} = (pgsT{2} + pqc{2}) %% Constants.R /\
  to_uint _25{1} = lqc{2} /\
  (0 <= lqc{2} && lqc{2} < Constants.R) /\
  (0 <= stateBetaPlusOne{2} && stateBetaPlusOne{2} < Constants.R) /\
  (0 <= stateBetaGammaPlusGamma{2} &&
   stateBetaGammaPlusGamma{2} < Constants.R) /\
  (0 <= stateZMinusLastOmega{2} && stateZMinusLastOmega{2} < Constants.R) /\
  Primops.memory{1} = m13 /\
  to_uint result{1} = lqcR{2} /\ lqcR{2} = (pqcR{2} + lqc{2}) %% Constants.R /\
  to_uint _27{1} = proofLinearisationPolyOpeningAtZ{2}
).
sp. 
call{1} (ConcretePrimops.mload_pspec m13 PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT).
skip. progress. rewrite /addmod. progress. 
rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils). rewrite /R_MOD. smt().
rewrite /m13 /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lookupQuotientContribution_memory_footprint /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 36! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT
        /STATE_Z_MINUS_LAST_OMEGA_SLOT
        /STATE_BETA_PLUS_ONE_SLOT
        /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT ; try by progress).

seq 3 1:(
  (stateAlpha{2}, stateBeta{2}, stateBetaLookup{2}, stateGamma{2},
   stateGammaLookup{2}, stateZ{2}, proofPublicInput{2},
   proofCopyPermutationPolys0OpeningAtZ{2},
   proofCopyPermutationPolys1OpeningAtZ{2},
   proofCopyPermutationPolys2OpeningAtZ{2}, proofStatePolys0OpeningAtZ{2},
   proofStatePolys1OpeningAtZ{2}, proofStatePolys2OpeningAtZ{2},
   proofStatePolys3OpeningAtZ{2}, proofLookupSPolyOpeningAtZOmega{2},
   proofLookupGrandProductOpeningAtZOmega{2},
   proofGateSelectors0OpeningAtZ{2}, proofLinearisationPolyOpeningAtZ{2},
   proofCopyPermutationGrandProductOpeningAtZOmega{2}, stateZInDomainSize{2},
   proofQuotientPolyOpeningAtZ{2}) =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG,
   stateZG, proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG,
   proofCopyPermutationPolys2OpeningAtZG, proofStatePolys0OpeningAtZG,
   proofStatePolys1OpeningAtZG, proofStatePolys2OpeningAtZG,
   proofStatePolys3OpeningAtZG, proofLookupSPolyOpeningAtZOmegaG,
   proofLookupGrandProductOpeningAtZOmegaG, proofGateSelectors0OpeningAtZG,
   proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
   proofQuotientPolyOpeningAtZG) /\
  to_uint (mload m STATE_ALPHA_SLOT) = stateAlphaG /\
  to_uint (mload m STATE_BETA_SLOT) = stateBetaG /\
  to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
  to_uint (mload m STATE_GAMMA_SLOT) = stateGammaG /\
  to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
  to_uint (mload m STATE_Z_SLOT) = stateZG /\
  to_uint (mload m PROOF_PUBLIC_INPUT) = proofPublicInputG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys0OpeningAtZG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys1OpeningAtZG /\
  to_uint (mload m PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
  proofCopyPermutationPolys2OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
  proofStatePolys0OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
  proofStatePolys1OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
  proofStatePolys2OpeningAtZG /\
  to_uint (mload m PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
  proofStatePolys3OpeningAtZG /\
  to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupSPolyOpeningAtZOmegaG /\
  to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupGrandProductOpeningAtZOmegaG /\
  to_uint (mload m PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
  proofGateSelectors0OpeningAtZG /\
  to_uint (mload m PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
  proofLinearisationPolyOpeningAtZG /\
  to_uint
    (mload m PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofCopyPermutationGrandProductOpeningAtZOmegaG /\
  to_uint (mload m STATE_Z_IN_DOMAIN_SIZE) = stateZInDomainSizeG /\
  to_uint (mload m PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
  proofQuotientPolyOpeningAtZG /\
  a = stateAlpha{2} /\
  a2 = statePowerOfAlpha2{2} /\
  a3 = statePowerOfAlpha3{2} /\
  a4 = statePowerOfAlpha4{2} /\
  a5 = statePowerOfAlpha5{2} /\
  a6 = statePowerOfAlpha6{2} /\
  a7 = statePowerOfAlpha7{2} /\
  a8 = statePowerOfAlpha8{2} /\
  statePowerOfAlpha2{2} = stateAlpha{2} ^ 2 %% Constants.R /\
  statePowerOfAlpha3{2} = stateAlpha{2} ^ 3 %% Constants.R /\
  statePowerOfAlpha4{2} = stateAlpha{2} ^ 4 %% Constants.R /\
  statePowerOfAlpha5{2} = stateAlpha{2} ^ 5 %% Constants.R /\
  statePowerOfAlpha6{2} = stateAlpha{2} ^ 6 %% Constants.R /\
  statePowerOfAlpha7{2} = stateAlpha{2} ^ 7 %% Constants.R /\
  statePowerOfAlpha8{2} = stateAlpha{2} ^ 8 %% Constants.R /\
  sbpo = stateBetaPlusOne{2} /\
  sbgpg = stateBetaGammaPlusGamma{2} /\
  szmlo = stateZMinusLastOmega{2} /\
  sl0az = _12{1} /\
  to_uint _12{1} = stateL0AtZ{2} /\
  slnm1az = _17{1} /\
  to_uint _17{1} = stateLnMinusOneAtZ{2} /\
  to_uint stateZ{1} = stateZ{2} /\
  (stateZ{2} ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
  elpodL0{2} = Some (to_uint _12{1}) /\
  elpodLn{2} = Some (to_uint _17{1}) /\
  (0 <= to_uint _12{1} && to_uint _12{1} < Constants.R) /\
  (0 <= to_uint _17{1} && to_uint _17{1} < Constants.R) /\
  !Primops.reverted{1} /\
  to_uint _20{1} = proofPublicInput{2} /\
  _21{1} = _12{1} /\
  to_uint stateT{1} = stateT{2} /\
  stateT{2} = stateL0AtZ{2} * proofPublicInput{2} %% Constants.R /\
  to_uint _23{1} = proofGateSelectors0OpeningAtZ{2} /\
  pgsT{2} = stateT{2} * proofGateSelectors0OpeningAtZ{2} %% Constants.R /\
  to_uint _24{1} = pqc{2} /\
  0 <= pqc{2} &&
  pqc{2} < Constants.R /\
  pqcR{2} = (pgsT{2} + pqc{2}) %% Constants.R /\
  to_uint _25{1} = lqc{2} /\
  (0 <= lqc{2} && lqc{2} < Constants.R) /\
  (0 <= stateBetaPlusOne{2} && stateBetaPlusOne{2} < Constants.R) /\
  (0 <= stateBetaGammaPlusGamma{2} &&
   stateBetaGammaPlusGamma{2} < Constants.R) /\
  (0 <= stateZMinusLastOmega{2} && stateZMinusLastOmega{2} < Constants.R) /\
  Primops.memory{1} = m13 /\
  lqcR{2} = (pqcR{2} + lqc{2}) %% Constants.R /\
  to_uint _27{1} = proofLinearisationPolyOpeningAtZ{2} /\
  to_uint result{1} = plpo{2} /\ plpo{2} = (proofLinearisationPolyOpeningAtZ{2} + lqcR{2}) %% Constants.R /\
  to_uint _28{1} = (Constants.R - 1) /\
  to_uint _30{1} = stateZInDomainSize{2}
).
sp.
call{1} (ConcretePrimops.mload_pspec m13 STATE_Z_IN_DOMAIN_SIZE).
skip. progress. rewrite /addmod. progress. 
rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils). rewrite /R_MOD. smt().
rewrite /R_MOD. smt().
rewrite /m13 /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lookupQuotientContribution_memory_footprint /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 36! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT
        /STATE_Z_MINUS_LAST_OMEGA_SLOT
        /STATE_BETA_PLUS_ONE_SLOT
        /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT
        /STATE_Z_IN_DOMAIN_SIZE ; try by progress).

seq 1 1:(#pre /\
  to_uint vanishing{1} = vanishing{2} /\
  vanishing{2} = (stateZInDomainSize{2} + (Constants.R - 1)) %% Constants.R).
wp. skip. progress. rewrite /addmod -H22. progress.
rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils). rewrite /R_MOD. smt().

seq 2 1: (#pre /\
  to_uint _32{1} = proofQuotientPolyOpeningAtZ{2} /\
  to_uint lhs{1} = lhs{2} /\
  lhs{2} = (proofQuotientPolyOpeningAtZ{2} * vanishing{2}) %% Constants.R).
wp. 
call{1} (ConcretePrimops.mload_pspec m13 PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT).
skip. progress.       
rewrite /m13 /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lookupQuotientContribution_memory_footprint /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 36! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT
        /STATE_Z_MINUS_LAST_OMEGA_SLOT
        /STATE_BETA_PLUS_ONE_SLOT
        /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT
        /STATE_Z_IN_DOMAIN_SIZE
        /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT ; try by progress).
rewrite /m13 /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1 /lookupQuotientContribution_memory_footprint /lagrange_memory_footprint /modexp_memory_footprint; progress.
do 36! (rewrite load_store_diff;
rewrite /STATE_Z_SLOT
        /STATE_POWER_OF_ALPHA_8_SLOT
        /STATE_POWER_OF_ALPHA_7_SLOT
        /STATE_POWER_OF_ALPHA_6_SLOT
        /STATE_POWER_OF_ALPHA_5_SLOT
        /STATE_POWER_OF_ALPHA_4_SLOT
        /STATE_POWER_OF_ALPHA_3_SLOT 
        /STATE_POWER_OF_ALPHA_2_SLOT
        /STATE_ALPHA_SLOT
        /STATE_BETA_SLOT
        /STATE_GAMMA_SLOT
        /STATE_BETA_LOOKUP_SLOT
        /STATE_GAMMA_LOOKUP_SLOT
        /PROOF_PUBLIC_INPUT
        /STATE_L_N_MINUS_ONE_AT_Z_SLOT
        /STATE_L_0_AT_Z_SLOT
        /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT
        /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
        /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
        /PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT
        /STATE_Z_MINUS_LAST_OMEGA_SLOT
        /STATE_BETA_PLUS_ONE_SLOT
        /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT
        /STATE_Z_IN_DOMAIN_SIZE
        /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT ; try by progress).
rewrite /mulmod. progress.
rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils).
rewrite /R_MOD. smt().

case (bool_of_uint256 (iszero (eq_uint256 lhs{1} result{1}))).
rcondt{1} 1. by progress.
seq 0 0: (
(stateZG ^ Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\ bool_of_uint256 (iszero (eq_uint256 lhs{1} result{1})) /\ to_uint lhs{1} = lhs{2} /\ to_uint result{1} = plpo{2}).
skip. progress. wp.
call{1} (revertWithMessage_low_pspec).
skip. progress. left. progress.
rewrite /eq_uint256 /iszero /bool_of_uint256 in H0. smt(@W256).

rcondf{1} 1. by progress.
wp. skip. progress. right. progress.
exists v1 v2 v3 v4 v5 v6 v7 v8. progress.
rewrite /eq_uint256 /iszero /bool_of_uint256 in H26. smt(@W256).
smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
qed.

lemma verifyQuotientEvaluation_mid_equiv_high_encapsulated (
      stateAlphaG
      stateBetaG
      stateBetaLookupG
      stateGammaG
      stateGammaLookupG
      stateZG
      proofPublicInputG
      proofCopyPermutationPolys0OpeningAtZG
      proofCopyPermutationPolys1OpeningAtZG
      proofCopyPermutationPolys2OpeningAtZG
      proofStatePolys0OpeningAtZG
      proofStatePolys1OpeningAtZG
      proofStatePolys2OpeningAtZG
      proofStatePolys3OpeningAtZG
      proofLookupSPolyOpeningAtZOmegaG
      proofLookupGrandProductOpeningAtZOmegaG
      proofGateSelectors0OpeningAtZG
      proofLinearisationPolyOpeningAtZG
      proofCopyPermutationGrandProductOpeningAtZOmegaG
      stateZInDomainSizeG
      proofQuotientPolyOpeningAtZG: FieldR.F
) :
    equiv [
      VerifyQuotientEvaluation.mid ~ VerifyQuotientEvaluation.high_encapsulated :
      arg{1} = (
        FieldR.asint stateAlphaG,
        FieldR.asint stateBetaG,
        FieldR.asint stateBetaLookupG,
        FieldR.asint stateGammaG,
        FieldR.asint stateGammaLookupG,
        FieldR.asint stateZG,
        FieldR.asint proofPublicInputG,
        FieldR.asint proofCopyPermutationPolys0OpeningAtZG,
        FieldR.asint proofCopyPermutationPolys1OpeningAtZG,
        FieldR.asint proofCopyPermutationPolys2OpeningAtZG,
        FieldR.asint proofStatePolys0OpeningAtZG,
        FieldR.asint proofStatePolys1OpeningAtZG,
        FieldR.asint proofStatePolys2OpeningAtZG,
        FieldR.asint proofStatePolys3OpeningAtZG,
        FieldR.asint proofLookupSPolyOpeningAtZOmegaG,
        FieldR.asint proofLookupGrandProductOpeningAtZOmegaG,
        FieldR.asint proofGateSelectors0OpeningAtZG,
        FieldR.asint proofLinearisationPolyOpeningAtZG,
        FieldR.asint proofCopyPermutationGrandProductOpeningAtZOmegaG,
        FieldR.asint stateZInDomainSizeG,
        FieldR.asint proofQuotientPolyOpeningAtZG
      ) /\
      arg{2} = (
        stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG, stateZG,
        proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
        proofCopyPermutationPolys1OpeningAtZG, proofCopyPermutationPolys2OpeningAtZG,
        proofStatePolys0OpeningAtZG, proofStatePolys1OpeningAtZG,
        proofStatePolys2OpeningAtZG, proofStatePolys3OpeningAtZG,
        proofLookupSPolyOpeningAtZOmegaG, proofLookupGrandProductOpeningAtZOmegaG,
        proofGateSelectors0OpeningAtZG, proofLinearisationPolyOpeningAtZG,
        proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
        proofQuotientPolyOpeningAtZG
      )
      ==>
  res{1}.`1 = res{2}.`1 /\
  (
    (res{1}.`1 = None)  \/
    (
      res{1}.`1 <> None /\
      stateZG ^ Constants.DOMAIN_SIZE - FieldR.one <> FieldR.zero /\
      res{1}.`2 = FieldR.asint res{2}.`2 /\
      res{1}.`3 = FieldR.asint res{2}.`3 /\
      res{1}.`4 = FieldR.asint res{2}.`4 /\
      res{1}.`5 = FieldR.asint res{2}.`5 /\
      res{1}.`6 = FieldR.asint res{2}.`6 /\
      res{1}.`7 = FieldR.asint res{2}.`7 /\
      res{1}.`8 = FieldR.asint res{2}.`8 /\
      res{1}.`9 = FieldR.asint res{2}.`9 /\
      res{1}.`10 = FieldR.asint res{2}.`10 /\
      res{1}.`11 = FieldR.asint res{2}.`11 /\
      res{1}.`12 = FieldR.asint res{2}.`12 /\
      res{1}.`13 = FieldR.asint res{2}.`13
    )
  )
  ].
proof.
  proc.
  seq 1 1 : (
    #pre /\
    statePowerOfAlpha2{2} = stateAlphaG ^2 /\
    statePowerOfAlpha2{1} = FieldR.asint statePowerOfAlpha2{2}
  ).  
  wp. skip. progress. 
  rewrite Constants.r_eq_fieldr_p -FieldR.mulE. by smt(@FieldR).
  seq 1 1 : (
    #pre /\ statePowerOfAlpha3{2} = stateAlphaG ^3 /\
    statePowerOfAlpha3{1} = FieldR.asint statePowerOfAlpha3{2}
  ).
  wp. skip. progress. 
  rewrite Constants.r_eq_fieldr_p. rewrite -IntDiv.modzMmr  -FieldR.mulE -FieldR.mulE. by smt(@FieldR).
  seq 1 1 : (
    #pre /\ statePowerOfAlpha4{2} = stateAlphaG ^4 /\
    statePowerOfAlpha4{1} = FieldR.asint statePowerOfAlpha4{2}
  ).
  wp. skip. progress. 
  rewrite Constants.r_eq_fieldr_p.
  have -> : stateAlpha{2} ^ 4 = stateAlpha{2} *  (stateAlpha{2} ^ 3) by smt(@FieldR).
    rewrite FieldR.mulE FieldR.eq_inF. do! rewrite FieldR.inFM. do! rewrite FieldR.asintK. congr. by smt(@FieldR).
  seq 1 1 : (
    #pre /\
    statePowerOfAlpha5{2} = stateAlphaG ^5 /\
    statePowerOfAlpha5{1} = FieldR.asint statePowerOfAlpha5{2}
  ).
  wp. skip. progress.
  rewrite Constants.r_eq_fieldr_p.
  have -> : stateAlpha{2} ^ 5 = stateAlpha{2} *  (stateAlpha{2} ^ 4) by smt(@FieldR).
    rewrite FieldR.mulE FieldR.eq_inF. do! rewrite FieldR.inFM. do! rewrite FieldR.asintK. congr. by smt(@FieldR).
  seq 1 1 : (
    #pre /\
    statePowerOfAlpha6{2} = stateAlphaG ^6 /\
    statePowerOfAlpha6{1} = FieldR.asint statePowerOfAlpha6{2}
  ).
  wp. skip. progress.
  rewrite Constants.r_eq_fieldr_p.
  have -> : stateAlpha{2} ^ 6 = stateAlpha{2} *  (stateAlpha{2} ^ 5) by smt(@FieldR).
    rewrite FieldR.mulE FieldR.eq_inF. do! rewrite FieldR.inFM. do! rewrite FieldR.asintK. congr. by smt(@FieldR).
  seq 1 1 : (
    #pre /\
    statePowerOfAlpha7{2} = stateAlphaG ^7 /\
    statePowerOfAlpha7{1} = FieldR.asint statePowerOfAlpha7{2}
  ).
  wp. skip. progress.
  rewrite Constants.r_eq_fieldr_p.
  have -> : stateAlpha{2} ^ 7 = stateAlpha{2} *  (stateAlpha{2} ^ 6) by smt(@FieldR).
    rewrite FieldR.mulE FieldR.eq_inF. do! rewrite FieldR.inFM. do! rewrite FieldR.asintK. congr. by smt(@FieldR).
  seq 1 1 : (
    #pre /\
    statePowerOfAlpha8{2} = stateAlphaG ^8 /\
    statePowerOfAlpha8{1} = FieldR.asint statePowerOfAlpha8{2}
  ).
  wp. skip. progress.
  rewrite Constants.r_eq_fieldr_p.
  have -> : stateAlpha{2} ^ 8 = stateAlpha{2} *  (stateAlpha{2} ^ 7) by smt(@FieldR).
  rewrite FieldR.mulE FieldR.eq_inF.
  do! rewrite FieldR.inFM.
  do! rewrite FieldR.asintK. congr.
  rewrite RexpE.
  do 7! (rewrite FieldR.ZrRing.expr_pred; first by trivial).
  rewrite FieldR.ZrRing.expr0.
  by smt(@FieldR).
 
   case (stateZG ^ Constants.DOMAIN_SIZE - FieldR.one = FieldR.zero).
  seq 1 1 : (
    #pre /\
    omap FieldR.asint elpodL0{2} = elpodL0{1} /\ (elpodL0{2} <> None <=> (stateZG^Constants.DOMAIN_SIZE - FieldR.one <> FieldR.zero))
  ).
  call{1} (evaluateLagrangePolyOutOfDomain_mid_equiv_high 0 stateZG).
  skip. by progress. 
  case (elpodL0{1} = None).
  if. progress. smt (). wp. skip. progress.
  seq 0 0 : (false).
  skip. progress. by smt().
  inline*. wp. skip. by progress. 
  if. by progress.
  sp. skip. by progress.
  seq 0 0 : (false).
  skip. progress. by smt().
  inline*. wp. skip. progress.
 seq 1 1 : (#pre /\ omap FieldR.asint elpodL0{2} = elpodL0{1} /\ (elpodL0{2} <> None <=> (stateZG^Constants.DOMAIN_SIZE - FieldR.one <> FieldR.zero))).
  call{1} (evaluateLagrangePolyOutOfDomain_mid_equiv_high 0 stateZG).
  skip. by progress.
case (elpodL0{1} = None).
  seq 0 0 : (false).
  skip. progress. by smt().
  inline*. wp. skip. by progress.
  if. by progress.
  sp. skip. by progress. 
  seq 1 1 : (
    #pre /\
    stateL0AtZ{1} = FieldR.asint stateL0AtZ{2}
  ).
  wp. skip. progress. by smt().
  seq 1 1 : (
    #pre /\
    elpodLn{1} = omap FieldR.asint elpodLn{2} /\
    is_some elpodLn{2}
  ).
  call{1} (evaluateLagrangePolyOutOfDomain_mid_equiv_high (Constants.DOMAIN_SIZE - 1) stateZG).
  skip. progress. rewrite /Constants.DOMAIN_SIZE. by progress.
  by smt(). 
  smt ().
  seq 1 1 : (
    #pre /\
    stateLnMinusOneAtZ{1} = FieldR.asint stateLnMinusOneAtZ{2}
  ).
  sp. skip. progress. rewrite /oget.
  by smt().
  seq 1 0 : (
    #pre /\
    stateT{1} = FieldR.asint (stateL0AtZ{2} * proofPublicInputG)
  ).
  wp. skip. progress.
  rewrite Constants.r_eq_fieldr_p. rewrite FieldR.mulE. reflexivity.
  seq 1 0 : (
    #pre /\
    pgsT{1} = FieldR.asint (stateL0AtZ{2} * proofPublicInputG * proofGateSelectors0OpeningAtZ{2})
  ).
  wp. skip. progress.
  rewrite Constants.r_eq_fieldr_p. smt (FieldR.mulE).
  seq 1 1 : (#pre /\ pqc{1} = FieldR.asint pqc{2}).
  exists* statePowerOfAlpha4{2}.
  elim* => statePowerOfAlpha4_L.
  exists* statePowerOfAlpha5{2}.
  elim* => statePowerOfAlpha5_L.
  exists* stateL0AtZ{2}.
  elim* => stateL0AtZ_L.
  call (permutationQuotientContribution_mid_equiv_high (statePowerOfAlpha4_L) (statePowerOfAlpha5_L)  proofCopyPermutationGrandProductOpeningAtZOmegaG stateBetaG stateGammaG
    proofCopyPermutationPolys0OpeningAtZG proofCopyPermutationPolys1OpeningAtZG proofCopyPermutationPolys2OpeningAtZG
    proofStatePolys0OpeningAtZG proofStatePolys1OpeningAtZG proofStatePolys2OpeningAtZG proofStatePolys3OpeningAtZG stateL0AtZ_L).
  skip. progress.
sp. wp.
  exists* stateLnMinusOneAtZ{2}.
  elim* => stateLnMinusOneAtZ_L.
  exists* statePowerOfAlpha6{2}.
  elim* => statePowerOfAlpha6_L.
  exists* statePowerOfAlpha7{2}.
  elim* => statePowerOfAlpha7_L.
  exists* statePowerOfAlpha8{2}.
  elim* => statePowerOfAlpha8_L.
    exists* stateL0AtZ{2}.
  elim* => stateL0AtZ_L.
  call (lookupQuotientContribution_mid_equiv_high stateBetaLookupG stateGammaLookupG statePowerOfAlpha6_L statePowerOfAlpha7_L statePowerOfAlpha8_L
        proofLookupSPolyOpeningAtZOmegaG proofLookupGrandProductOpeningAtZOmegaG stateZG stateL0AtZ_L stateLnMinusOneAtZ_L).
  skip. progress.
  rewrite H4.
  rewrite Constants.r_eq_fieldr_p.
  rewrite FieldR.eq_inF.
  have ->: forall (x y: FieldR.F), FieldR.inF (
    (FieldR.asint x) * (
      (
        (FieldR.asint y) +
        (FieldR.p - 1)
      ) %% FieldR.p
    )) = (x * (y + -FieldR.one)).
    progress.
    have ->: FieldR.p - 1 = FieldR.asint (-FieldR.one) by smt(@FieldR @IntDiv).
    rewrite -FieldR.addE.
    rewrite FieldR.inF_mod.
    rewrite -FieldR.mulE.
    rewrite FieldR.asintK.
    reflexivity.
  have ->: forall (a b c d e f: FieldR.F), (FieldR.inF
    ((FieldR.asint a) + (((FieldR.asint (b * c * d)) + (FieldR.asint e)) %% FieldR.p + (FieldR.asint f)) %% FieldR.p)) =
     (a + b * c * d + e + f).
    progress.
    rewrite -FieldR.addE.
    rewrite -FieldR.addE.
    rewrite FieldR.inF_mod.
    rewrite -FieldR.addE.
    rewrite FieldR.asintK.
    smt (@FieldR).
  reflexivity.
qed.
  
lemma verifyQuotientEvaluation_high_encapsulated_equiv_high' (
      stateAlphaG
      stateBetaG
      stateBetaLookupG
      stateGammaG
      stateGammaLookupG
      stateZG
      proofPublicInputG
      proofCopyPermutationPolys0OpeningAtZG
      proofCopyPermutationPolys1OpeningAtZG
      proofCopyPermutationPolys2OpeningAtZG
      proofStatePolys0OpeningAtZG
      proofStatePolys1OpeningAtZG
      proofStatePolys2OpeningAtZG
      proofStatePolys3OpeningAtZG
      proofLookupSPolyOpeningAtZOmegaG
      proofLookupGrandProductOpeningAtZOmegaG
      proofGateSelectors0OpeningAtZG
      proofLinearisationPolyOpeningAtZG
      proofCopyPermutationGrandProductOpeningAtZOmegaG
      stateZInDomainSizeG
      proofQuotientPolyOpeningAtZG: FieldR.F
) :
equiv [VerifyQuotientEvaluation.high_encapsulated ~ VerifyQuotientEvaluation.high' :
={arg} /\
arg{1} =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG, stateZG,
   proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG, proofCopyPermutationPolys2OpeningAtZG,
   proofStatePolys0OpeningAtZG, proofStatePolys1OpeningAtZG,
   proofStatePolys2OpeningAtZG, proofStatePolys3OpeningAtZG,
   proofLookupSPolyOpeningAtZOmegaG, proofLookupGrandProductOpeningAtZOmegaG,
   proofGateSelectors0OpeningAtZG, proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG)
  ==>
res{1}.`1 = res{2}.`1 /\
  (res{1}.`1 <> None =>
    stateZG ^ Constants.DOMAIN_SIZE <> FieldR.one /\
  res{1}.`2 = res{2}.`2 /\
  res{1}.`3 = res{2}.`3 /\
  res{1}.`4 = res{2}.`4 /\
  res{1}.`5 = res{2}.`5 /\
  res{1}.`6 = res{2}.`6 /\
  res{1}.`7 = res{2}.`7 /\
  res{1}.`8 = res{2}.`8 /\
  res{1}.`9 = res{2}.`9 /\
  res{1}.`10 = res{2}.`10 /\
  res{1}.`11 = res{2}.`11 /\
    res{1}.`12 = res{2}.`12 /\
    res{1}.`13 = res{2}.`13)
].
proof.
  proc.
  seq 7 7 : (#pre /\ ={statePowerOfAlpha2, statePowerOfAlpha3, statePowerOfAlpha4, statePowerOfAlpha5, statePowerOfAlpha6, statePowerOfAlpha7, statePowerOfAlpha8}).
  wp. skip. by progress.
  case (stateZG ^ Constants.DOMAIN_SIZE = FieldR.one).
  seq 1 1 : (#pre /\ elpodL0{1} = None /\ stateZAtDomainSize{2} = FieldR.one).
  inline*. rcondt{1} 6. progress. wp. skip. progress. rewrite H. by smt(@FieldR).
  sp. skip. by progress.
  rcondt{1} 1. by progress.
  rcondt{2} 1. by progress.
  wp. skip. progress.
  seq 0 1 : (#pre /\ stateZAtDomainSize{2} = stateZG ^ Constants.DOMAIN_SIZE).
  wp. skip. by progress. 
  seq 1 0 : (#pre /\ elpodL0{1} = Some (((stateZAtDomainSize{2} - FieldR.one) * (Constants.DOMAIN_SIZEFr * (stateZG - FieldR.one)) ^ -1))).
  inline*. rcondf{1} 6. progress. wp. skip. progress. by smt(@FieldR).
  wp. skip. progress. by smt(@FieldR).
  rcondf{1} 1. by progress.
  rcondf{2} 1. by progress. 
  seq 1 1 : (#pre /\ ={stateL0AtZ}).
  wp. skip. by progress. 
  seq 1 0 : (#pre /\ elpodLn{1} = Some (Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1) * (stateZAtDomainSize{2} - FieldR.one) * (Constants.DOMAIN_SIZEFr * (stateZG - Constants.OMEGAFr^(Constants.DOMAIN_SIZE - 1))) ^ -1)).
  inline*. 
  rcondf{1} 6. progress.
  wp. skip. progress. by smt(@FieldR). 
  wp. skip. progress.
  seq 1 1 : (#pre /\ ={stateLnMinusOneAtZ}). 
  wp. skip. by progress. 
  seq 1 1 : (#pre /\ ={pqc}).  
  inline*. wp. skip. by progress. 
  seq 1 1 : (#pre /\ ={lqc, stateBetaPlusOne, stateBetaGammaPlusGamma, stateZMinusLastOmega}).
  inline*. wp. skip. by progress.
  wp. skip. by progress.
qed. 

lemma verifyQuotientEvaluation_high'_equiv_high (
      stateAlphaG
      stateBetaG
      stateBetaLookupG
      stateGammaG
      stateGammaLookupG
      stateZG
      proofPublicInputG
      proofCopyPermutationPolys0OpeningAtZG
      proofCopyPermutationPolys1OpeningAtZG
      proofCopyPermutationPolys2OpeningAtZG
      proofStatePolys0OpeningAtZG
      proofStatePolys1OpeningAtZG
      proofStatePolys2OpeningAtZG
      proofStatePolys3OpeningAtZG
      proofLookupSPolyOpeningAtZOmegaG
      proofLookupGrandProductOpeningAtZOmegaG
      proofGateSelectors0OpeningAtZG
      proofLinearisationPolyOpeningAtZG
      proofCopyPermutationGrandProductOpeningAtZOmegaG
      stateZInDomainSizeG
      proofQuotientPolyOpeningAtZG: FieldR.F
) :
equiv [VerifyQuotientEvaluation.high' ~ VerifyQuotientEvaluation.high :
={arg} /\
arg{1} =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG, stateZG,
   proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG, proofCopyPermutationPolys2OpeningAtZG,
   proofStatePolys0OpeningAtZG, proofStatePolys1OpeningAtZG,
   proofStatePolys2OpeningAtZG, proofStatePolys3OpeningAtZG,
   proofLookupSPolyOpeningAtZOmegaG, proofLookupGrandProductOpeningAtZOmegaG,
   proofGateSelectors0OpeningAtZG, proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG)
  ==>
res{1}.`1 = res{2}.`1 /\
  (res{1}.`1 <> None =>
    stateZG ^ Constants.DOMAIN_SIZE <> FieldR.one /\
  res{1}.`2 = res{2}.`2 /\
  res{1}.`3 = res{2}.`3 /\
  res{1}.`4 = res{2}.`4 /\
  res{1}.`5 = res{2}.`5 /\
  res{1}.`6 = res{2}.`6 /\
  res{1}.`7 = res{2}.`7 /\
  res{1}.`8 = res{2}.`8 /\
  res{1}.`9 = res{2}.`9 /\
  res{1}.`10 = res{2}.`10 /\
  res{1}.`11 = res{2}.`11 /\
    res{1}.`12 = res{2}.`12 /\
    res{1}.`13 = res{2}.`13)].
proof.
  proc.
  seq 8 0 : (#pre /\ statePowerOfAlpha2{1} = stateAlphaG ^ 2 /\ statePowerOfAlpha3{1} = stateAlphaG ^ 3
  /\ statePowerOfAlpha4{1} = stateAlphaG ^ 4 /\ statePowerOfAlpha5{1} = stateAlphaG ^ 5 /\ statePowerOfAlpha6{1} = stateAlphaG ^ 6
  /\ statePowerOfAlpha7{1} = stateAlphaG ^ 7 /\ statePowerOfAlpha8{1} = stateAlphaG ^ 8 /\ stateZAtDomainSize{1} = stateZG ^ Constants.DOMAIN_SIZE).
  wp. skip. by progress.
  case (stateZG ^ Constants.DOMAIN_SIZE = FieldR.one).
  rcondt{1} 1. by progress.
  rcondt{2} 1. by progress.
  wp. skip. by progress.
  rcondf{1} 1. by progress.
  rcondf{2} 1. by progress.
  seq 2 2 : (#pre /\ ={stateL0AtZ, stateLnMinusOneAtZ}).
  wp. skip. by progress.
  wp. skip. progress. 
  by smt (@FieldR). by smt(@FieldR).
qed.

lemma verifyQuotientEvaluation_mid_equiv_high (
      stateAlphaG
      stateBetaG
      stateBetaLookupG
      stateGammaG
      stateGammaLookupG
      stateZG
      proofPublicInputG
      proofCopyPermutationPolys0OpeningAtZG
      proofCopyPermutationPolys1OpeningAtZG
      proofCopyPermutationPolys2OpeningAtZG
      proofStatePolys0OpeningAtZG
      proofStatePolys1OpeningAtZG
      proofStatePolys2OpeningAtZG
      proofStatePolys3OpeningAtZG
      proofLookupSPolyOpeningAtZOmegaG
      proofLookupGrandProductOpeningAtZOmegaG
      proofGateSelectors0OpeningAtZG
      proofLinearisationPolyOpeningAtZG
      proofCopyPermutationGrandProductOpeningAtZOmegaG
      stateZInDomainSizeG
      proofQuotientPolyOpeningAtZG: FieldR.F
) :
equiv [VerifyQuotientEvaluation.mid ~ VerifyQuotientEvaluation.high :
arg{1} = (FieldR.asint stateAlphaG, FieldR.asint stateBetaG, FieldR.asint stateBetaLookupG, FieldR.asint stateGammaG, FieldR.asint stateGammaLookupG, FieldR.asint stateZG,
   FieldR.asint proofPublicInputG, FieldR.asint proofCopyPermutationPolys0OpeningAtZG,
   FieldR.asint proofCopyPermutationPolys1OpeningAtZG, FieldR.asint proofCopyPermutationPolys2OpeningAtZG,
   FieldR.asint proofStatePolys0OpeningAtZG, FieldR.asint proofStatePolys1OpeningAtZG,
   FieldR.asint proofStatePolys2OpeningAtZG, FieldR.asint proofStatePolys3OpeningAtZG,
   FieldR.asint proofLookupSPolyOpeningAtZOmegaG, FieldR.asint proofLookupGrandProductOpeningAtZOmegaG,
   FieldR.asint proofGateSelectors0OpeningAtZG, FieldR.asint proofLinearisationPolyOpeningAtZG,
   FieldR.asint proofCopyPermutationGrandProductOpeningAtZOmegaG, FieldR.asint stateZInDomainSizeG,
   FieldR.asint proofQuotientPolyOpeningAtZG) /\
arg{2} =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG, stateZG,
   proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG, proofCopyPermutationPolys2OpeningAtZG,
   proofStatePolys0OpeningAtZG, proofStatePolys1OpeningAtZG,
   proofStatePolys2OpeningAtZG, proofStatePolys3OpeningAtZG,
   proofLookupSPolyOpeningAtZOmegaG, proofLookupGrandProductOpeningAtZOmegaG,
   proofGateSelectors0OpeningAtZG, proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG)
==>
  res{1}.`1 = res{2}.`1 /\
  (
    (res{1}.`1 = None)  \/
    (
      res{1}.`1 <> None /\
      stateZG ^ Constants.DOMAIN_SIZE - FieldR.one <> FieldR.zero /\
      res{1}.`2 = FieldR.asint res{2}.`2 /\
      res{1}.`3 = FieldR.asint res{2}.`3 /\
      res{1}.`4 = FieldR.asint res{2}.`4 /\
      res{1}.`5 = FieldR.asint res{2}.`5 /\
      res{1}.`6 = FieldR.asint res{2}.`6 /\
      res{1}.`7 = FieldR.asint res{2}.`7 /\
      res{1}.`8 = FieldR.asint res{2}.`8 /\
      res{1}.`9 = FieldR.asint res{2}.`9 /\
      res{1}.`10 = FieldR.asint res{2}.`10 /\
      res{1}.`11 = FieldR.asint res{2}.`11 /\
      res{1}.`12 = FieldR.asint res{2}.`12 /\
      res{1}.`13 = FieldR.asint res{2}.`13
    )
  )].
proof.
  transitivity VerifyQuotientEvaluation.high_encapsulated
    (arg{1} = (FieldR.asint stateAlphaG, FieldR.asint stateBetaG, FieldR.asint stateBetaLookupG, FieldR.asint stateGammaG, FieldR.asint stateGammaLookupG, FieldR.asint stateZG,
   FieldR.asint proofPublicInputG, FieldR.asint proofCopyPermutationPolys0OpeningAtZG,
   FieldR.asint proofCopyPermutationPolys1OpeningAtZG, FieldR.asint proofCopyPermutationPolys2OpeningAtZG,
   FieldR.asint proofStatePolys0OpeningAtZG, FieldR.asint proofStatePolys1OpeningAtZG,
   FieldR.asint proofStatePolys2OpeningAtZG, FieldR.asint proofStatePolys3OpeningAtZG,
   FieldR.asint proofLookupSPolyOpeningAtZOmegaG, FieldR.asint proofLookupGrandProductOpeningAtZOmegaG,
   FieldR.asint proofGateSelectors0OpeningAtZG, FieldR.asint proofLinearisationPolyOpeningAtZG,
   FieldR.asint proofCopyPermutationGrandProductOpeningAtZOmegaG, FieldR.asint stateZInDomainSizeG,
   FieldR.asint proofQuotientPolyOpeningAtZG) /\
arg{2} =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG, stateZG,
   proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG, proofCopyPermutationPolys2OpeningAtZG,
   proofStatePolys0OpeningAtZG, proofStatePolys1OpeningAtZG,
   proofStatePolys2OpeningAtZG, proofStatePolys3OpeningAtZG,
   proofLookupSPolyOpeningAtZOmegaG, proofLookupGrandProductOpeningAtZOmegaG,
   proofGateSelectors0OpeningAtZG, proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG)
==>
  res{1}.`1 = res{2}.`1 /\
  (
    (res{1}.`1 = None)  \/
    (
      res{1}.`1 <> None /\
      stateZG ^ Constants.DOMAIN_SIZE - FieldR.one <> FieldR.zero /\
      res{1}.`2 = FieldR.asint res{2}.`2 /\
      res{1}.`3 = FieldR.asint res{2}.`3 /\
      res{1}.`4 = FieldR.asint res{2}.`4 /\
      res{1}.`5 = FieldR.asint res{2}.`5 /\
      res{1}.`6 = FieldR.asint res{2}.`6 /\
      res{1}.`7 = FieldR.asint res{2}.`7 /\
      res{1}.`8 = FieldR.asint res{2}.`8 /\
      res{1}.`9 = FieldR.asint res{2}.`9 /\
      res{1}.`10 = FieldR.asint res{2}.`10 /\
      res{1}.`11 = FieldR.asint res{2}.`11 /\
      res{1}.`12 = FieldR.asint res{2}.`12 /\
      res{1}.`13 = FieldR.asint res{2}.`13
    )
  ))
  (={arg} /\
arg{1} =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG, stateZG,
   proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG, proofCopyPermutationPolys2OpeningAtZG,
   proofStatePolys0OpeningAtZG, proofStatePolys1OpeningAtZG,
   proofStatePolys2OpeningAtZG, proofStatePolys3OpeningAtZG,
   proofLookupSPolyOpeningAtZOmegaG, proofLookupGrandProductOpeningAtZOmegaG,
   proofGateSelectors0OpeningAtZG, proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG)
  ==>
res{1}.`1 = res{2}.`1 /\
  (res{1}.`1 <> None =>
    stateZG ^ Constants.DOMAIN_SIZE <> FieldR.one /\
  res{1}.`2 = res{2}.`2 /\
  res{1}.`3 = res{2}.`3 /\
  res{1}.`4 = res{2}.`4 /\
  res{1}.`5 = res{2}.`5 /\
  res{1}.`6 = res{2}.`6 /\
  res{1}.`7 = res{2}.`7 /\
  res{1}.`8 = res{2}.`8 /\
  res{1}.`9 = res{2}.`9 /\
  res{1}.`10 = res{2}.`10 /\
  res{1}.`11 = res{2}.`11 /\
    res{1}.`12 = res{2}.`12 /\
    res{1}.`13 = res{2}.`13)).
    by smt(). by smt(). exact verifyQuotientEvaluation_mid_equiv_high_encapsulated.
  transitivity VerifyQuotientEvaluation.high'
    (={arg} /\
arg{1} =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG, stateZG,
   proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG, proofCopyPermutationPolys2OpeningAtZG,
   proofStatePolys0OpeningAtZG, proofStatePolys1OpeningAtZG,
   proofStatePolys2OpeningAtZG, proofStatePolys3OpeningAtZG,
   proofLookupSPolyOpeningAtZOmegaG, proofLookupGrandProductOpeningAtZOmegaG,
   proofGateSelectors0OpeningAtZG, proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG)
  ==>
res{1}.`1 = res{2}.`1 /\
  (res{1}.`1 <> None =>
    stateZG ^ Constants.DOMAIN_SIZE <> FieldR.one /\
  res{1}.`2 = res{2}.`2 /\
  res{1}.`3 = res{2}.`3 /\
  res{1}.`4 = res{2}.`4 /\
  res{1}.`5 = res{2}.`5 /\
  res{1}.`6 = res{2}.`6 /\
  res{1}.`7 = res{2}.`7 /\
  res{1}.`8 = res{2}.`8 /\
  res{1}.`9 = res{2}.`9 /\
  res{1}.`10 = res{2}.`10 /\
  res{1}.`11 = res{2}.`11 /\
    res{1}.`12 = res{2}.`12 /\
    res{1}.`13 = res{2}.`13))
  (={arg} /\
arg{1} =
  (stateAlphaG, stateBetaG, stateBetaLookupG, stateGammaG, stateGammaLookupG, stateZG,
   proofPublicInputG, proofCopyPermutationPolys0OpeningAtZG,
   proofCopyPermutationPolys1OpeningAtZG, proofCopyPermutationPolys2OpeningAtZG,
   proofStatePolys0OpeningAtZG, proofStatePolys1OpeningAtZG,
   proofStatePolys2OpeningAtZG, proofStatePolys3OpeningAtZG,
   proofLookupSPolyOpeningAtZOmegaG, proofLookupGrandProductOpeningAtZOmegaG,
   proofGateSelectors0OpeningAtZG, proofLinearisationPolyOpeningAtZG,
   proofCopyPermutationGrandProductOpeningAtZOmegaG, stateZInDomainSizeG,
    proofQuotientPolyOpeningAtZG)
  ==>
res{1}.`1 = res{2}.`1 /\
  (res{1}.`1 <> None =>
    stateZG ^ Constants.DOMAIN_SIZE <> FieldR.one /\
  res{1}.`2 = res{2}.`2 /\
  res{1}.`3 = res{2}.`3 /\
  res{1}.`4 = res{2}.`4 /\
  res{1}.`5 = res{2}.`5 /\
  res{1}.`6 = res{2}.`6 /\
  res{1}.`7 = res{2}.`7 /\
  res{1}.`8 = res{2}.`8 /\
  res{1}.`9 = res{2}.`9 /\
  res{1}.`10 = res{2}.`10 /\
  res{1}.`11 = res{2}.`11 /\
    res{1}.`12 = res{2}.`12 /\
    res{1}.`13 = res{2}.`13)).
    by smt(). by smt(). exact verifyQuotientEvaluation_high_encapsulated_equiv_high'.
    exact verifyQuotientEvaluation_high'_equiv_high.
qed. 
