require import AllCore.
require import Int.
require import IntDiv.
require        Constants.
require import Field.
require import Modexp.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module LookupQuotientContribution = {
  proc low(): uint256 = {
    var ret, betaLookup, gammaLookup, betaPlusOne, betaGamma, _8, _10, _12, lastOmega, _18, zMinusLastOmega, _21, _23, intermediateValue, lnMinusOneAtZ, betaGammaPowered, alphaPower8, _27, subtrahend : uint256;
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

  proc mid (
      stateBetaLookup
      stateGammaLookup
      statePowerOfAlpha6
      statePowerOfAlpha7
      statePowerOfAlpha8
      proofLookupSPolyOpeningAtZOmega
      proofLookupGrandProductOpeningAtZOmega
      stateZ
      stateL0AtZ
      stateLnMinusOneAtZ
      : int) = {
    var betaPlusOne, betaGamma, lastOmega, zMinusLastOmega, betaGammaPowered: int;
    var f, a6c, a6c', a7c, a8c: int;

    betaPlusOne <- (stateBetaLookup + 1) %% Constants.R;
    betaGamma <- (stateGammaLookup * betaPlusOne) %% Constants.R;
    f <- (proofLookupSPolyOpeningAtZOmega * stateBetaLookup + betaGamma) %% Constants.R;
    a6c' <- (statePowerOfAlpha6 * f * proofLookupGrandProductOpeningAtZOmega) %% Constants.R;
    lastOmega <@ Modexp.mid(Constants.OMEGA, (Constants.DOMAIN_SIZE - 1));
    zMinusLastOmega <- (stateZ - lastOmega) %% Constants.R;
    a6c <- (a6c' * zMinusLastOmega) %% Constants.R; 
    a7c <- (statePowerOfAlpha7 * stateL0AtZ) %% Constants.R;
    betaGammaPowered <@ Modexp.mid(betaGamma, Constants.DOMAIN_SIZE - 1);
    a8c <- (statePowerOfAlpha8 * stateLnMinusOneAtZ * betaGammaPowered) %% Constants.R;

    return ((a6c - a7c - a8c) %% Constants.R, betaPlusOne, betaGamma, zMinusLastOmega);
  }

  proc high(stateBetaLookup
      stateGammaLookup
      statePowerOfAlpha6
      statePowerOfAlpha7
      statePowerOfAlpha8
      proofLookupSPolyOpeningAtZOmega
      proofLookupGrandProductOpeningAtZOmega
      stateZ
      stateL0AtZ
      stateLnMinusOneAtZ
      : FieldR.F) = {
    return (
      ((statePowerOfAlpha6 * (proofLookupSPolyOpeningAtZOmega * stateBetaLookup + stateGammaLookup * (stateBetaLookup + FieldR.one)) * proofLookupGrandProductOpeningAtZOmega) * (stateZ - Constants.OMEGAFr ^(Constants.DOMAIN_SIZE - 1)) 
        - statePowerOfAlpha7 * stateL0AtZ 
        - statePowerOfAlpha8 * stateLnMinusOneAtZ * (stateGammaLookup * (stateBetaLookup + FieldR.one)) ^ (Constants.DOMAIN_SIZE - 1)), 
        (stateBetaLookup + FieldR.one), 
        stateGammaLookup * (stateBetaLookup + FieldR.one), 
        stateZ - Constants.OMEGAFr ^(Constants.DOMAIN_SIZE - 1));

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
      seq 2 1: (#pre /\ usr_betaGammaPowered{1} = betaGammaPowered{2}). wp. call modexp_extracted_equiv_low. skip. by progress. 
      seq 3 1: (#pre /\ usr_alphaPower8{1} = alphaPower8{2}). inline*. wp. skip. by progress.
      seq 2 2: (#pre /\ usr_subtrahend{1} = subtrahend{2}). wp. skip. rewrite /Constants.R. by progress.
      wp. skip. rewrite /Constants.R. by progress.
    qed.

lemma lookupQuotientContribution_pspec_revert :
phoare [ LookupQuotientContribution.low : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; inline*; wp; skip; by auto. qed.
    
section.
import MemoryMap PurePrimops.
declare op m : mem.

op lookupQuotientContribution_memory_footprint 
  (lastOmega
   betaPlusOne
   betaGamma
   zMinusLastOmega v : uint256)
  =
  let m1 = store m STATE_BETA_PLUS_ONE_SLOT betaPlusOne in
  let m2 = store m1 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT betaGamma in
  let m3 = modexp_memory_footprint m2 OMEGA (DOMAIN_SIZE - W256.one) lastOmega in
  let m4 = store m3 STATE_Z_MINUS_LAST_OMEGA_SLOT zMinusLastOmega in
  let m5 = modexp_memory_footprint m4 betaGamma (DOMAIN_SIZE - W256.one) v in
  m5.

lemma lookupQuotientContribution_low_equiv_mid (
stateBetaLookupG
stateGammaLookupG
statePowerOfAlpha6G
statePowerOfAlpha7G
statePowerOfAlpha8G
proofLookupSPolyOpeningAtZOmegaG
proofLookupGrandProductOpeningAtZOmegaG
stateZG
stateL0AtZG
stateLnMinusOneAtZG : int
) :
equiv [LookupQuotientContribution.low ~ LookupQuotientContribution.mid :
arg{2} =
  (stateBetaLookupG, stateGammaLookupG, statePowerOfAlpha6G,
   statePowerOfAlpha7G, statePowerOfAlpha8G, proofLookupSPolyOpeningAtZOmegaG,
   proofLookupGrandProductOpeningAtZOmegaG, stateZG, stateL0AtZG, stateLnMinusOneAtZG) /\
Primops.memory{1} = m /\
!Primops.reverted{1} /\
W256.to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
W256.to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
W256.to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) = statePowerOfAlpha6G /\
W256.to_uint (mload m STATE_POWER_OF_ALPHA_7_SLOT) = statePowerOfAlpha7G /\
W256.to_uint (mload m STATE_POWER_OF_ALPHA_8_SLOT) = statePowerOfAlpha8G /\
W256.to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
W256.to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
W256.to_uint (mload m STATE_Z_SLOT) = stateZG /\
W256.to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZG /\
W256.to_uint (mload m STATE_L_N_MINUS_ONE_AT_Z_SLOT) = stateLnMinusOneAtZG
==>
!Primops.reverted{1} /\
exists v1 v2, 
Primops.memory{1} =
  lookupQuotientContribution_memory_footprint
     (W256.of_int v1) (W256.of_int res{2}.`2) (W256.of_int res{2}.`3) (W256.of_int res{2}.`4) (W256.of_int v2) /\
res{2}.`1 = W256.to_uint res{1} /\
0 <= res{2}.`1 < Constants.R /\
0 <= res{2}.`2 < Constants.R /\
0 <= res{2}.`3 < Constants.R /\
0 <= res{2}.`4 < Constants.R
].
proof. proc. simplify.
seq 2 0: (#pre /\
  W256.to_uint betaLookup{1} = stateBetaLookupG /\
  W256.to_uint gammaLookup{1} = stateGammaLookupG).
call{1} (ConcretePrimops.mload_pspec m STATE_GAMMA_LOOKUP_SLOT).
call{1} (ConcretePrimops.mload_pspec m STATE_BETA_LOOKUP_SLOT).
skip. by progress.

seq 2 2 : (#pre /\
  W256.to_uint betaPlusOne{1} = betaPlusOne{2} /\ betaPlusOne{2} = (stateBetaLookup{2} + 1) %% Constants.R /\
  W256.to_uint betaGamma{1} = betaGamma{2} /\ betaGamma{2} = (stateGammaLookup{2} * betaPlusOne{2}) %% Constants.R).
wp. skip. rewrite /addmod /mulmod. progress.
rewrite H0. by smt. 
rewrite H0 H1. by smt.

exists* betaPlusOne{1}. elim*=> bpo. exists* betaGamma{1}. elim*=> bg.
pose m1 := store m STATE_BETA_PLUS_ONE_SLOT bpo.
pose m2 := store m1 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT bg.
seq 2 0: (
!Primops.reverted{1} /\
bg = betaGamma{1} /\
bpo = betaPlusOne{1} /\
stateBetaLookup{2} = stateBetaLookupG /\
stateGammaLookup{2} = stateGammaLookupG /\
statePowerOfAlpha6{2} = statePowerOfAlpha6G /\
statePowerOfAlpha7{2} = statePowerOfAlpha7G /\
statePowerOfAlpha8{2} = statePowerOfAlpha8G /\
proofLookupSPolyOpeningAtZOmega{2} =
proofLookupSPolyOpeningAtZOmegaG /\
proofLookupGrandProductOpeningAtZOmega{2} =
proofLookupGrandProductOpeningAtZOmegaG /\
stateZ{2} = stateZG /\
stateL0AtZ{2} = stateL0AtZG /\
stateLnMinusOneAtZ{2} = stateLnMinusOneAtZG /\
to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) = statePowerOfAlpha6G /\
to_uint (mload m STATE_POWER_OF_ALPHA_7_SLOT) = statePowerOfAlpha7G /\
to_uint (mload m STATE_POWER_OF_ALPHA_8_SLOT) = statePowerOfAlpha8G /\
to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupSPolyOpeningAtZOmegaG /\
to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmegaG /\
to_uint (mload m STATE_Z_SLOT) = stateZG /\
to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZG /\
to_uint (mload m STATE_L_N_MINUS_ONE_AT_Z_SLOT) = stateLnMinusOneAtZG /\

to_uint betaLookup{1} = stateBetaLookupG /\
to_uint gammaLookup{1} = stateGammaLookupG /\
to_uint betaPlusOne{1} = betaPlusOne{2} /\
betaPlusOne{2} = (stateBetaLookup{2} + 1) %% Constants.R /\
to_uint betaGamma{1} = betaGamma{2} /\
betaGamma{2} = stateGammaLookup{2} * betaPlusOne{2} %% Constants.R /\
Primops.memory{1} = m2
).
call{1} (ConcretePrimops.mstore_pspec m1 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT bg).
call{1} (ConcretePrimops.mstore_pspec m STATE_BETA_PLUS_ONE_SLOT bpo).
skip. by progress.

seq 1 0: (#pre /\ to_uint _8{1} = proofLookupSPolyOpeningAtZOmega{2}).
call{1} (ConcretePrimops.mload_pspec m2 PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT).
skip; progress; rewrite /m2 /m1. 
rewrite load_store_diff;
rewrite /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT; try by auto.
rewrite load_store_diff;
rewrite /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT /STATE_BETA_PLUS_ONE_SLOT; try by smt().

seq 1 0: (#pre /\
  to_uint ret{1} = (proofLookupSPolyOpeningAtZOmega{2} * stateBetaLookup{2}) %% Constants.R
).
wp. skip. progress. rewrite /mulmod H4 H0. progress. smt.
seq 1 1:(
  !Primops.reverted{1} /\
    bg = betaGamma{1} /\
    bpo = betaPlusOne{1} /\
    stateBetaLookup{2} = stateBetaLookupG /\
    stateGammaLookup{2} = stateGammaLookupG /\
    statePowerOfAlpha6{2} = statePowerOfAlpha6G /\
    statePowerOfAlpha7{2} = statePowerOfAlpha7G /\
    statePowerOfAlpha8{2} = statePowerOfAlpha8G /\
    proofLookupSPolyOpeningAtZOmega{2} =
    proofLookupSPolyOpeningAtZOmegaG /\
    proofLookupGrandProductOpeningAtZOmega{2} =
    proofLookupGrandProductOpeningAtZOmegaG /\
    stateZ{2} = stateZG /\
    stateL0AtZ{2} = stateL0AtZG /\
    stateLnMinusOneAtZ{2} = stateLnMinusOneAtZG /\
    to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
    to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
    to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) = statePowerOfAlpha6G /\
    to_uint (mload m STATE_POWER_OF_ALPHA_7_SLOT) = statePowerOfAlpha7G /\
    to_uint (mload m STATE_POWER_OF_ALPHA_8_SLOT) = statePowerOfAlpha8G /\
    to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
    proofLookupSPolyOpeningAtZOmegaG /\
    to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
    proofLookupGrandProductOpeningAtZOmegaG /\
    to_uint (mload m STATE_Z_SLOT) = stateZG /\
    to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZG /\
    to_uint (mload m STATE_L_N_MINUS_ONE_AT_Z_SLOT) = stateLnMinusOneAtZG /\
    
    to_uint betaLookup{1} = stateBetaLookupG /\
    to_uint gammaLookup{1} = stateGammaLookupG /\
    to_uint betaPlusOne{1} = betaPlusOne{2} /\
    betaPlusOne{2} = (stateBetaLookup{2} + 1) %% Constants.R /\
    to_uint betaGamma{1} = betaGamma{2} /\
    betaGamma{2} = stateGammaLookup{2} * betaPlusOne{2} %% Constants.R /\
    Primops.memory{1} = m2 /\
   to_uint _8{1} = proofLookupSPolyOpeningAtZOmega{2} /\
  to_uint ret{1} = f{2} /\
  f{2} = (proofLookupSPolyOpeningAtZOmega{2} * stateBetaLookup{2} + betaGamma{2}) %% Constants.R
).
wp. skip. progress. rewrite /addmod H5 H3 H2. progress. smt timeout=10.

seq 1 0: (#pre /\ to_uint _10{1} = proofLookupGrandProductOpeningAtZOmega{2}).
call{1} (ConcretePrimops.mload_pspec m2 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT).
skip. progress. rewrite /m2 /m1. 
rewrite load_store_diff;
rewrite /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /STATE_BETA_PLUS_ONE_SLOT; try by auto.
rewrite load_store_diff;
rewrite /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT /STATE_BETA_PLUS_ONE_SLOT; try by smt().

seq 2 0:(
  !Primops.reverted{1} /\
   bg = betaGamma{1} /\
   bpo = betaPlusOne{1} /\
   stateBetaLookup{2} = stateBetaLookupG /\
   stateGammaLookup{2} = stateGammaLookupG /\
   statePowerOfAlpha6{2} = statePowerOfAlpha6G /\
   statePowerOfAlpha7{2} = statePowerOfAlpha7G /\
   statePowerOfAlpha8{2} = statePowerOfAlpha8G /\
   proofLookupSPolyOpeningAtZOmega{2} =
   proofLookupSPolyOpeningAtZOmegaG /\
   proofLookupGrandProductOpeningAtZOmega{2} =
   proofLookupGrandProductOpeningAtZOmegaG /\
   stateZ{2} = stateZG /\
   stateL0AtZ{2} = stateL0AtZG /\
   stateLnMinusOneAtZ{2} = stateLnMinusOneAtZG /\
   to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
   to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
   to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) = statePowerOfAlpha6G /\
   to_uint (mload m STATE_POWER_OF_ALPHA_7_SLOT) = statePowerOfAlpha7G /\
   to_uint (mload m STATE_POWER_OF_ALPHA_8_SLOT) = statePowerOfAlpha8G /\
   to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupSPolyOpeningAtZOmegaG /\
   to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupGrandProductOpeningAtZOmegaG /\
   to_uint (mload m STATE_Z_SLOT) = stateZG /\
   to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZG /\
   to_uint (mload m STATE_L_N_MINUS_ONE_AT_Z_SLOT) = stateLnMinusOneAtZG /\
   
   to_uint betaLookup{1} = stateBetaLookupG /\
   to_uint gammaLookup{1} = stateGammaLookupG /\
   to_uint betaPlusOne{1} = betaPlusOne{2} /\
   betaPlusOne{2} = (stateBetaLookup{2} + 1) %% Constants.R /\
   to_uint betaGamma{1} = betaGamma{2} /\
   betaGamma{2} = stateGammaLookup{2} * betaPlusOne{2} %% Constants.R /\
   Primops.memory{1} = m2 /\
   to_uint _8{1} = proofLookupSPolyOpeningAtZOmega{2} /\
   f{2} = (proofLookupSPolyOpeningAtZOmega{2} * stateBetaLookup{2} + betaGamma{2}) %% Constants.R /\
   to_uint _10{1} = proofLookupGrandProductOpeningAtZOmega{2} /\
   to_uint ret{1} = (f{2} * proofLookupGrandProductOpeningAtZOmega{2}) %% Constants.R /\
   to_uint _12{1} = statePowerOfAlpha6{2}
).
sp.
call{1} (ConcretePrimops.mload_pspec m2 STATE_POWER_OF_ALPHA_6_SLOT).
skip. progress. rewrite /mulmod. progress. rewrite H5 H6. smt.
rewrite /m2 /m1. 
rewrite load_store_diff;
rewrite /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_6_SLOT; try by auto.
rewrite load_store_diff;
rewrite /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT /STATE_BETA_PLUS_ONE_SLOT; try by smt().

seq 1 1: (
  !Primops.reverted{1} /\
  bg = betaGamma{1} /\
  bpo = betaPlusOne{1} /\
  stateBetaLookup{2} = stateBetaLookupG /\
  stateGammaLookup{2} = stateGammaLookupG /\
  statePowerOfAlpha6{2} = statePowerOfAlpha6G /\
  statePowerOfAlpha7{2} = statePowerOfAlpha7G /\
  statePowerOfAlpha8{2} = statePowerOfAlpha8G /\
  proofLookupSPolyOpeningAtZOmega{2} =
  proofLookupSPolyOpeningAtZOmegaG /\
  proofLookupGrandProductOpeningAtZOmega{2} =
  proofLookupGrandProductOpeningAtZOmegaG /\
  stateZ{2} = stateZG /\
  stateL0AtZ{2} = stateL0AtZG /\
  stateLnMinusOneAtZ{2} = stateLnMinusOneAtZG /\
  to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
  to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
  to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) = statePowerOfAlpha6G /\
  to_uint (mload m STATE_POWER_OF_ALPHA_7_SLOT) = statePowerOfAlpha7G /\
  to_uint (mload m STATE_POWER_OF_ALPHA_8_SLOT) = statePowerOfAlpha8G /\
  to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupSPolyOpeningAtZOmegaG /\
  to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupGrandProductOpeningAtZOmegaG /\
  to_uint (mload m STATE_Z_SLOT) = stateZG /\
  to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZG /\
  to_uint (mload m STATE_L_N_MINUS_ONE_AT_Z_SLOT) = stateLnMinusOneAtZG /\
  
  to_uint betaLookup{1} = stateBetaLookupG /\
  to_uint gammaLookup{1} = stateGammaLookupG /\
  to_uint betaPlusOne{1} = betaPlusOne{2} /\
  betaPlusOne{2} = (stateBetaLookup{2} + 1) %% Constants.R /\
  to_uint betaGamma{1} = betaGamma{2} /\
  betaGamma{2} = stateGammaLookup{2} * betaPlusOne{2} %% Constants.R /\
  Primops.memory{1} = m2 /\
  to_uint _8{1} = proofLookupSPolyOpeningAtZOmega{2} /\
  f{2} = (proofLookupSPolyOpeningAtZOmega{2} * stateBetaLookup{2} + betaGamma{2}) %% Constants.R /\
  to_uint _10{1} = proofLookupGrandProductOpeningAtZOmega{2} /\
  to_uint _12{1} = statePowerOfAlpha6{2} /\
  to_uint ret{1} = a6c'{2} /\
  a6c'{2} = (statePowerOfAlpha6{2} * f{2} * proofLookupGrandProductOpeningAtZOmega{2}) %% Constants.R
).
wp. skip. progress. rewrite /mulmod. progress.
rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils).
rewrite H6 H7. rewrite W256.to_uint_small. progress. by smt.

seq 1 1:(
  !Primops.reverted{1} /\
  bg = betaGamma{1} /\
  bpo = betaPlusOne{1} /\
  stateBetaLookup{2} = stateBetaLookupG /\
  stateGammaLookup{2} = stateGammaLookupG /\
  statePowerOfAlpha6{2} = statePowerOfAlpha6G /\
  statePowerOfAlpha7{2} = statePowerOfAlpha7G /\
  statePowerOfAlpha8{2} = statePowerOfAlpha8G /\
  proofLookupSPolyOpeningAtZOmega{2} =
  proofLookupSPolyOpeningAtZOmegaG /\
  proofLookupGrandProductOpeningAtZOmega{2} =
  proofLookupGrandProductOpeningAtZOmegaG /\
  stateZ{2} = stateZG /\
  stateL0AtZ{2} = stateL0AtZG /\
  stateLnMinusOneAtZ{2} = stateLnMinusOneAtZG /\
  to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
  to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
  to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) = statePowerOfAlpha6G /\
  to_uint (mload m STATE_POWER_OF_ALPHA_7_SLOT) = statePowerOfAlpha7G /\
  to_uint (mload m STATE_POWER_OF_ALPHA_8_SLOT) = statePowerOfAlpha8G /\
  to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupSPolyOpeningAtZOmegaG /\
  to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupGrandProductOpeningAtZOmegaG /\
  to_uint (mload m STATE_Z_SLOT) = stateZG /\
  to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZG /\
  to_uint (mload m STATE_L_N_MINUS_ONE_AT_Z_SLOT) = stateLnMinusOneAtZG /\
  
  to_uint betaLookup{1} = stateBetaLookupG /\
  to_uint gammaLookup{1} = stateGammaLookupG /\
  to_uint betaPlusOne{1} = betaPlusOne{2} /\
  betaPlusOne{2} = (stateBetaLookup{2} + 1) %% Constants.R /\
  to_uint betaGamma{1} = betaGamma{2} /\
  betaGamma{2} = stateGammaLookup{2} * betaPlusOne{2} %% Constants.R /\
  to_uint _8{1} = proofLookupSPolyOpeningAtZOmega{2} /\
  f{2} =
  (proofLookupSPolyOpeningAtZOmega{2} * stateBetaLookup{2} +
   betaGamma{2}) %%
  Constants.R /\
  to_uint _10{1} = proofLookupGrandProductOpeningAtZOmega{2} /\
  to_uint _12{1} = statePowerOfAlpha6{2} /\
  to_uint ret{1} = a6c'{2} /\
  a6c'{2} =
  statePowerOfAlpha6{2} * f{2} *
  proofLookupGrandProductOpeningAtZOmega{2} %% Constants.R /\
  Primops.memory{1} = modexp_memory_footprint m2 OMEGA (DOMAIN_SIZE - W256.one) lastOmega{1} /\
  to_uint lastOmega{1} = lastOmega{2} /\
  0 <= lastOmega{2} < Constants.R
).
call (modexp_low_equiv_mid m2 OMEGA (DOMAIN_SIZE - W256.one)).
skip. progress. rewrite /OMEGA. by smt(). rewrite /DOMAIN_SIZE. by progress.
exists* lastOmega{1}. elim* => ol.
pose m3 := modexp_memory_footprint m2 OMEGA (DOMAIN_SIZE - W256.one) ol.

seq 1 0 : (#pre /\ to_uint _18{1} = stateZ{2}).
call{1} (ConcretePrimops.mload_pspec m3 STATE_Z_SLOT).
skip. progress. rewrite /m3 /m2 /m1 /modexp_memory_footprint. progress.  
rewrite load_store_diff /STATE_Z_SLOT. by progress. by progress.
do 6! (rewrite load_store_diff; try by progress). 
rewrite /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT. by progress.
rewrite load_store_diff /STATE_BETA_PLUS_ONE_SLOT. by progress. by progress. by smt().

seq 1 1: (#pre /\
  to_uint zMinusLastOmega{1} = zMinusLastOmega{2} /\
  zMinusLastOmega{2} = (stateZ{2} - lastOmega{2}) %% Constants.R).
wp. skip. progress. rewrite /addmod H10. progress.
rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils). 
have ->: (to_uint (mload m STATE_Z_SLOT) - to_uint lastOmega{1}) %% Constants.R = (to_uint (mload m STATE_Z_SLOT) + (Constants.R - to_uint lastOmega{1})) %% Constants.R. by smt().
rewrite to_uintB. by smt. by smt.

exists* zMinusLastOmega{1}. elim* => zmlo.
pose m4 := store m3 STATE_Z_MINUS_LAST_OMEGA_SLOT zmlo.
seq 1 0:(
!Primops.reverted{1} /\
  zmlo = zMinusLastOmega{1} /\
  ol = lastOmega{1} /\
    bg = betaGamma{1} /\
    bpo = betaPlusOne{1} /\
    stateBetaLookup{2} = stateBetaLookupG /\
    stateGammaLookup{2} = stateGammaLookupG /\
    statePowerOfAlpha6{2} = statePowerOfAlpha6G /\
    statePowerOfAlpha7{2} = statePowerOfAlpha7G /\
    statePowerOfAlpha8{2} = statePowerOfAlpha8G /\
    proofLookupSPolyOpeningAtZOmega{2} =
    proofLookupSPolyOpeningAtZOmegaG /\
    proofLookupGrandProductOpeningAtZOmega{2} =
    proofLookupGrandProductOpeningAtZOmegaG /\
    stateZ{2} = stateZG /\
    stateL0AtZ{2} = stateL0AtZG /\
    stateLnMinusOneAtZ{2} = stateLnMinusOneAtZG /\
    to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
    to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
    to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) = statePowerOfAlpha6G /\
    to_uint (mload m STATE_POWER_OF_ALPHA_7_SLOT) = statePowerOfAlpha7G /\
    to_uint (mload m STATE_POWER_OF_ALPHA_8_SLOT) = statePowerOfAlpha8G /\
    to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
    proofLookupSPolyOpeningAtZOmegaG /\
    to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
    proofLookupGrandProductOpeningAtZOmegaG /\
    to_uint (mload m STATE_Z_SLOT) = stateZG /\
    to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZG /\
    to_uint (mload m STATE_L_N_MINUS_ONE_AT_Z_SLOT) = stateLnMinusOneAtZG /\
    to_uint betaLookup{1} = stateBetaLookupG /\
    to_uint gammaLookup{1} = stateGammaLookupG /\
    to_uint betaPlusOne{1} = betaPlusOne{2} /\
    betaPlusOne{2} = (stateBetaLookup{2} + 1) %% Constants.R /\
    to_uint betaGamma{1} = betaGamma{2} /\
    betaGamma{2} = stateGammaLookup{2} * betaPlusOne{2} %% Constants.R /\
    to_uint _8{1} = proofLookupSPolyOpeningAtZOmega{2} /\
    f{2} =
    (proofLookupSPolyOpeningAtZOmega{2} * stateBetaLookup{2} +
     betaGamma{2}) %%
    Constants.R /\
    to_uint _10{1} = proofLookupGrandProductOpeningAtZOmega{2} /\
    to_uint _12{1} = statePowerOfAlpha6{2} /\
    to_uint ret{1} = a6c'{2} /\
    a6c'{2} =
    statePowerOfAlpha6{2} * f{2} *
    proofLookupGrandProductOpeningAtZOmega{2} %% Constants.R /\
    to_uint lastOmega{1} = lastOmega{2} /\
    0 <= lastOmega{2} && lastOmega{2} < Constants.R /\
   to_uint _18{1} = stateZ{2} /\
  to_uint zMinusLastOmega{1} = zMinusLastOmega{2} /\
  zMinusLastOmega{2} = (stateZ{2} - lastOmega{2}) %% Constants.R /\
  Primops.memory{1} = m4
).
call{1} (ConcretePrimops.mstore_pspec m3 STATE_Z_MINUS_LAST_OMEGA_SLOT zmlo).
skip. by progress.

seq 3 1:(
  !Primops.reverted{1} /\
  zmlo = zMinusLastOmega{1} /\
  ol = lastOmega{1} /\
  bg = betaGamma{1} /\
  bpo = betaPlusOne{1} /\
  stateBetaLookup{2} = stateBetaLookupG /\
  stateGammaLookup{2} = stateGammaLookupG /\
  statePowerOfAlpha6{2} = statePowerOfAlpha6G /\
  statePowerOfAlpha7{2} = statePowerOfAlpha7G /\
  statePowerOfAlpha8{2} = statePowerOfAlpha8G /\
  proofLookupSPolyOpeningAtZOmega{2} =
  proofLookupSPolyOpeningAtZOmegaG /\
  proofLookupGrandProductOpeningAtZOmega{2} =
  proofLookupGrandProductOpeningAtZOmegaG /\
  stateZ{2} = stateZG /\
  stateL0AtZ{2} = stateL0AtZG /\
  stateLnMinusOneAtZ{2} = stateLnMinusOneAtZG /\
  to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
  to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
  to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) = statePowerOfAlpha6G /\
  to_uint (mload m STATE_POWER_OF_ALPHA_7_SLOT) = statePowerOfAlpha7G /\
  to_uint (mload m STATE_POWER_OF_ALPHA_8_SLOT) = statePowerOfAlpha8G /\
  to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupSPolyOpeningAtZOmegaG /\
  to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
  proofLookupGrandProductOpeningAtZOmegaG /\
  to_uint (mload m STATE_Z_SLOT) = stateZG /\
  to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZG /\
  to_uint (mload m STATE_L_N_MINUS_ONE_AT_Z_SLOT) = stateLnMinusOneAtZG /\
  
  to_uint betaLookup{1} = stateBetaLookupG /\
  to_uint gammaLookup{1} = stateGammaLookupG /\
  to_uint betaPlusOne{1} = betaPlusOne{2} /\
  betaPlusOne{2} = (stateBetaLookup{2} + 1) %% Constants.R /\
  to_uint betaGamma{1} = betaGamma{2} /\
  betaGamma{2} = stateGammaLookup{2} * betaPlusOne{2} %% Constants.R /\
  to_uint _8{1} = proofLookupSPolyOpeningAtZOmega{2} /\
  f{2} =
  (proofLookupSPolyOpeningAtZOmega{2} * stateBetaLookup{2} +
   betaGamma{2}) %%
  Constants.R /\
  to_uint _10{1} = proofLookupGrandProductOpeningAtZOmega{2} /\
  to_uint _12{1} = statePowerOfAlpha6{2} /\
  a6c'{2} =
  statePowerOfAlpha6{2} * f{2} *
  proofLookupGrandProductOpeningAtZOmega{2} %% Constants.R /\
  to_uint lastOmega{1} = lastOmega{2} /\
  0 <= lastOmega{2} &&
  lastOmega{2} < Constants.R /\
  to_uint _18{1} = stateZ{2} /\
  to_uint zMinusLastOmega{1} = zMinusLastOmega{2} /\
  zMinusLastOmega{2} = (stateZ{2} - lastOmega{2}) %% Constants.R /\
  Primops.memory{1} = m4 /\
  to_uint ret{1} = a6c{2} /\ a6c{2} = (a6c'{2} * zMinusLastOmega{2}) %% Constants.R /\
  to_uint _21{1} = statePowerOfAlpha7{2} /\
  to_uint _23{1} = stateL0AtZ{2}
).
sp.
call{1} (ConcretePrimops.mload_pspec m4 STATE_L_0_AT_Z_SLOT).
call{1} (ConcretePrimops.mload_pspec m4 STATE_POWER_OF_ALPHA_7_SLOT).
skip. progress. rewrite /mulmod. progress. rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils). smt.
rewrite /m4 /m3 /m2 /m1 /modexp_memory_footprint. progress.  
rewrite load_store_diff /STATE_POWER_OF_ALPHA_7_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT. by progress. by progress.
do 7! (rewrite load_store_diff; try by progress). 
rewrite /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT. by progress.
rewrite load_store_diff /STATE_BETA_PLUS_ONE_SLOT. by smt(). by smt(). by smt().
rewrite /m4 /m3 /m2 /m1 /modexp_memory_footprint. progress.  
rewrite load_store_diff /STATE_POWER_OF_ALPHA_7_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT /STATE_L_0_AT_Z_SLOT. by progress. by progress.
do 7! (rewrite load_store_diff; try by progress). 
rewrite /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT. by progress.
rewrite load_store_diff /STATE_BETA_PLUS_ONE_SLOT. by smt(). by smt(). by smt().

seq 1 1: (#pre /\
  to_uint intermediateValue{1} = a7c{2} /\
  a7c{2} = (statePowerOfAlpha7{2} * stateL0AtZ{2}) %% Constants.R).
wp. skip. rewrite /mulmod. progress. rewrite W256.to_uint_small. progress. smt(@W256 @Utils). smt(@W256 @Utils). rewrite H12 H13. smt. 

seq 1 0:(
  !Primops.reverted{1} /\
   zmlo = zMinusLastOmega{1} /\
   ol = lastOmega{1} /\
   bg = betaGamma{1} /\
   bpo = betaPlusOne{1} /\
   stateBetaLookup{2} = stateBetaLookupG /\
   stateGammaLookup{2} = stateGammaLookupG /\
   statePowerOfAlpha6{2} = statePowerOfAlpha6G /\
   statePowerOfAlpha7{2} = statePowerOfAlpha7G /\
   statePowerOfAlpha8{2} = statePowerOfAlpha8G /\
   proofLookupSPolyOpeningAtZOmega{2} =
   proofLookupSPolyOpeningAtZOmegaG /\
   proofLookupGrandProductOpeningAtZOmega{2} =
   proofLookupGrandProductOpeningAtZOmegaG /\
   stateZ{2} = stateZG /\
   stateL0AtZ{2} = stateL0AtZG /\
   stateLnMinusOneAtZ{2} = stateLnMinusOneAtZG /\
   to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
   to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
   to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) = statePowerOfAlpha6G /\
   to_uint (mload m STATE_POWER_OF_ALPHA_7_SLOT) = statePowerOfAlpha7G /\
   to_uint (mload m STATE_POWER_OF_ALPHA_8_SLOT) = statePowerOfAlpha8G /\
   to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupSPolyOpeningAtZOmegaG /\
   to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupGrandProductOpeningAtZOmegaG /\
   to_uint (mload m STATE_Z_SLOT) = stateZG /\
   to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZG /\
   to_uint (mload m STATE_L_N_MINUS_ONE_AT_Z_SLOT) = stateLnMinusOneAtZG /\
   
   to_uint betaLookup{1} = stateBetaLookupG /\
   to_uint gammaLookup{1} = stateGammaLookupG /\
   to_uint betaPlusOne{1} = betaPlusOne{2} /\
   betaPlusOne{2} = (stateBetaLookup{2} + 1) %% Constants.R /\
   to_uint betaGamma{1} = betaGamma{2} /\
   betaGamma{2} = stateGammaLookup{2} * betaPlusOne{2} %% Constants.R /\
   to_uint _8{1} = proofLookupSPolyOpeningAtZOmega{2} /\
   f{2} =
   (proofLookupSPolyOpeningAtZOmega{2} * stateBetaLookup{2} +
    betaGamma{2}) %%
   Constants.R /\
   to_uint _10{1} = proofLookupGrandProductOpeningAtZOmega{2} /\
   to_uint _12{1} = statePowerOfAlpha6{2} /\
   a6c'{2} =
   statePowerOfAlpha6{2} * f{2} *
   proofLookupGrandProductOpeningAtZOmega{2} %% Constants.R /\
   to_uint lastOmega{1} = lastOmega{2} /\
   0 <= lastOmega{2} &&
   lastOmega{2} < Constants.R /\
   to_uint _18{1} = stateZ{2} /\
   to_uint zMinusLastOmega{1} = zMinusLastOmega{2} /\
   zMinusLastOmega{2} = (stateZ{2} - lastOmega{2}) %% Constants.R /\
   Primops.memory{1} = m4 /\
   a6c{2} = (a6c'{2} * zMinusLastOmega{2}) %% Constants.R /\
   to_uint _21{1} = statePowerOfAlpha7{2} /\
   to_uint _23{1} = stateL0AtZ{2} /\
  to_uint intermediateValue{1} = a7c{2} /\
  a7c{2} = (statePowerOfAlpha7{2} * stateL0AtZ{2}) %% Constants.R /\
   to_uint ret{1} = (a6c{2} - a7c{2}) %% Constants.R
).
wp. skip. rewrite /addmod. progress.
rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils).
have ->: (to_uint ret{1} - to_uint intermediateValue{1}) %% Constants.R = (to_uint ret{1} + (Constants.R - to_uint intermediateValue{1})) %% Constants.R. smt().
rewrite to_uintB. smt timeout=10. smt.

seq 1 0: (#pre /\ to_uint lnMinusOneAtZ{1} = stateLnMinusOneAtZ{2}).
call{1} (ConcretePrimops.mload_pspec m4 STATE_L_N_MINUS_ONE_AT_Z_SLOT).
skip. progress. rewrite /m4 /m3 /m2 /m1 /modexp_memory_footprint. progress.  
rewrite load_store_diff /STATE_POWER_OF_ALPHA_7_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT /STATE_L_N_MINUS_ONE_AT_Z_SLOT. by progress. by progress.
do 7! (rewrite load_store_diff; try by progress). 
rewrite /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT. by progress.
rewrite load_store_diff /STATE_BETA_PLUS_ONE_SLOT. by smt(). by smt(). by smt().

seq 1 1: (
   !Primops.reverted{1} /\
   zmlo = zMinusLastOmega{1} /\
   ol = lastOmega{1} /\
   bg = betaGamma{1} /\
   bpo = betaPlusOne{1} /\
   stateBetaLookup{2} = stateBetaLookupG /\
   stateGammaLookup{2} = stateGammaLookupG /\
   statePowerOfAlpha6{2} = statePowerOfAlpha6G /\
   statePowerOfAlpha7{2} = statePowerOfAlpha7G /\
   statePowerOfAlpha8{2} = statePowerOfAlpha8G /\
   proofLookupSPolyOpeningAtZOmega{2} =
   proofLookupSPolyOpeningAtZOmegaG /\
   proofLookupGrandProductOpeningAtZOmega{2} =
   proofLookupGrandProductOpeningAtZOmegaG /\
   stateZ{2} = stateZG /\
   stateL0AtZ{2} = stateL0AtZG /\
   stateLnMinusOneAtZ{2} = stateLnMinusOneAtZG /\
   to_uint (mload m STATE_BETA_LOOKUP_SLOT) = stateBetaLookupG /\
   to_uint (mload m STATE_GAMMA_LOOKUP_SLOT) = stateGammaLookupG /\
   to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) = statePowerOfAlpha6G /\
   to_uint (mload m STATE_POWER_OF_ALPHA_7_SLOT) = statePowerOfAlpha7G /\
   to_uint (mload m STATE_POWER_OF_ALPHA_8_SLOT) = statePowerOfAlpha8G /\
   to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupSPolyOpeningAtZOmegaG /\
   to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   proofLookupGrandProductOpeningAtZOmegaG /\
   to_uint (mload m STATE_Z_SLOT) = stateZG /\
   to_uint (mload m STATE_L_0_AT_Z_SLOT) = stateL0AtZG /\
   to_uint (mload m STATE_L_N_MINUS_ONE_AT_Z_SLOT) = stateLnMinusOneAtZG /\
   to_uint betaLookup{1} = stateBetaLookupG /\
   to_uint gammaLookup{1} = stateGammaLookupG /\
   to_uint betaPlusOne{1} = betaPlusOne{2} /\
   betaPlusOne{2} = (stateBetaLookup{2} + 1) %% Constants.R /\
   to_uint betaGamma{1} = betaGamma{2} /\
   betaGamma{2} = stateGammaLookup{2} * betaPlusOne{2} %% Constants.R /\
   to_uint _8{1} = proofLookupSPolyOpeningAtZOmega{2} /\
   f{2} =
   (proofLookupSPolyOpeningAtZOmega{2} * stateBetaLookup{2} +
    betaGamma{2}) %%
   Constants.R /\
   to_uint _10{1} = proofLookupGrandProductOpeningAtZOmega{2} /\
   to_uint _12{1} = statePowerOfAlpha6{2} /\
   a6c'{2} =
   statePowerOfAlpha6{2} * f{2} *
   proofLookupGrandProductOpeningAtZOmega{2} %% Constants.R /\
   to_uint lastOmega{1} = lastOmega{2} /\
   0 <= lastOmega{2} &&
   lastOmega{2} < Constants.R /\
   to_uint _18{1} = stateZ{2} /\
   to_uint zMinusLastOmega{1} = zMinusLastOmega{2} /\
   zMinusLastOmega{2} = (stateZ{2} - lastOmega{2}) %% Constants.R /\
   a6c{2} = a6c'{2} * zMinusLastOmega{2} %% Constants.R /\
   to_uint _21{1} = statePowerOfAlpha7{2} /\
   to_uint _23{1} = stateL0AtZ{2} /\
   to_uint intermediateValue{1} = a7c{2} /\
   a7c{2} = statePowerOfAlpha7{2} * stateL0AtZ{2} %% Constants.R /\
   to_uint ret{1} = (a6c{2} - a7c{2}) %% Constants.R /\
   to_uint lnMinusOneAtZ{1} = stateLnMinusOneAtZ{2} /\
   Primops.memory{1} = modexp_memory_footprint m4 betaGamma{1} (DOMAIN_SIZE - W256.one) betaGammaPowered{1} /\
   to_uint betaGammaPowered{1} = betaGammaPowered{2} /\ 0 <= betaGammaPowered{2} < Constants.R
).
call (modexp_low_equiv_mid m4 bg (DOMAIN_SIZE - W256.one)).
skip. progress. rewrite /DOMAIN_SIZE. by progress.
exists* betaGammaPowered{1}. elim* => bgp.
pose m5 := modexp_memory_footprint m4 bg (DOMAIN_SIZE - W256.one) bgp.

seq 1 0: (#pre /\ to_uint alphaPower8{1} = statePowerOfAlpha8{2}).
call{1} (ConcretePrimops.mload_pspec m5 STATE_POWER_OF_ALPHA_8_SLOT).
skip. progress. rewrite /m5 /m4 /m3 /m2 /m1 /modexp_memory_footprint. progress.  
rewrite load_store_diff /STATE_POWER_OF_ALPHA_7_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT /STATE_L_N_MINUS_ONE_AT_Z_SLOT /STATE_POWER_OF_ALPHA_8_SLOT. by progress. by progress.
do 13! (rewrite load_store_diff; try by progress). 
rewrite /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT. by progress.
rewrite load_store_diff /STATE_BETA_PLUS_ONE_SLOT. by smt(). by smt(). by smt().

seq 1 0: (#pre /\ to_uint _27{1} = (stateLnMinusOneAtZ{2} * betaGammaPowered{2}) %% Constants.R).
wp. skip. rewrite /mulmod. progress. rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils).
rewrite H15. smt.

seq 1 1: (#pre /\ to_uint subtrahend{1} = a8c{2} /\
  a8c{2} = (statePowerOfAlpha8{2} * stateLnMinusOneAtZ{2} * betaGammaPowered{2}) %% Constants.R).
wp. skip. rewrite /mulmod. progress. rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils).
rewrite H19 H18. rewrite W256.to_uint_small. progress. by smt.

wp. skip. progress. exists (to_uint lastOmega{1}) (to_uint betaGammaPowered{1}). progress.
rewrite /addmod. progress. rewrite W256.to_uint_small. progress. by smt(@W256 @Utils). by smt(@W256 @Utils).
pose lala := (to_uint (mload m STATE_POWER_OF_ALPHA_6_SLOT) *
 ((to_uint (mload m PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) *
   to_uint (mload m STATE_BETA_LOOKUP_SLOT) + to_uint betaGamma{1}) %%
  Constants.R) *
 to_uint (mload m PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) %%
 Constants.R * to_uint zMinusLastOmega{1} %% Constants.R -
 to_uint intermediateValue{1}).
have ->: (lala - to_uint subtrahend{1}) %% Constants.R = (lala + (Constants.R - to_uint subtrahend{1})) %% Constants.R. smt().
rewrite to_uintB. smt timeout=10. rewrite /lala H14. smt.
smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
qed.

end section.

lemma lookupQuotientContribution_mid_equiv_high (
stateBetaLookupG
stateGammaLookupG
statePowerOfAlpha6G
statePowerOfAlpha7G
statePowerOfAlpha8G
proofLookupSPolyOpeningAtZOmegaG
proofLookupGrandProductOpeningAtZOmegaG
stateZG
stateL0AtZG
stateLnMinusOneAtZG : FieldR.F
) :
equiv [LookupQuotientContribution.mid ~ LookupQuotientContribution.high :
arg{1} = (FieldR.asint stateBetaLookupG, FieldR.asint stateGammaLookupG, FieldR.asint statePowerOfAlpha6G,
   FieldR.asint statePowerOfAlpha7G, FieldR.asint statePowerOfAlpha8G, FieldR.asint proofLookupSPolyOpeningAtZOmegaG,
   FieldR.asint proofLookupGrandProductOpeningAtZOmegaG, FieldR.asint stateZG, FieldR.asint stateL0AtZG, FieldR.asint stateLnMinusOneAtZG) /\
arg{2} =
  (stateBetaLookupG, stateGammaLookupG, statePowerOfAlpha6G,
   statePowerOfAlpha7G, statePowerOfAlpha8G, proofLookupSPolyOpeningAtZOmegaG,
   proofLookupGrandProductOpeningAtZOmegaG, stateZG, stateL0AtZG, stateLnMinusOneAtZG)
==>
  res{1}.`1 = FieldR.asint res{2}.`1 /\
  res{1}.`2 = FieldR.asint res{2}.`2 /\
  res{1}.`3 = FieldR.asint res{2}.`3 /\
  res{1}.`4 = FieldR.asint res{2}.`4
].
proof. 
proc. 
seq 1 0 : (#pre /\ betaPlusOne{1} = FieldR.asint (stateBetaLookupG + FieldR.one)).
wp. skip. progress. 
rewrite Constants.r_eq_fieldr_p. rewrite FieldR.addE. smt (@FieldR).
seq 1 0 : (#pre /\ betaGamma{1} = FieldR.asint (stateGammaLookupG * (stateBetaLookupG + FieldR.one))).
wp. skip. progress. 
rewrite Constants.r_eq_fieldr_p. smt (@FieldR).
seq 1 0 : (#pre /\ f{1} = FieldR.asint (proofLookupSPolyOpeningAtZOmegaG * stateBetaLookupG + stateGammaLookupG * (stateBetaLookupG + FieldR.one))).
wp. skip. progress. 
rewrite Constants.r_eq_fieldr_p. rewrite FieldR.addE. rewrite FieldR.mulE. rewrite FieldR.mulE. smt (@FieldR @IntDiv).
seq 1 0 : (#pre /\ a6c'{1} = FieldR.asint (statePowerOfAlpha6G * (proofLookupSPolyOpeningAtZOmegaG * stateBetaLookupG + stateGammaLookupG * (stateBetaLookupG + FieldR.one)) * proofLookupGrandProductOpeningAtZOmegaG)).
wp. skip. progress. 
rewrite Constants.r_eq_fieldr_p. smt (@FieldR @IntDiv).
seq 1 0 : (#pre /\ lastOmega{1} = FieldR.asint (Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1))).
inline*. wp. skip. progress. 
rewrite Constants.r_eq_fieldr_p. smt (@FieldR @IntDiv @Constants).
seq 1 0 : (#pre /\ zMinusLastOmega{1} = FieldR.asint (stateZG - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1))).
wp. skip. progress. 
rewrite Constants.r_eq_fieldr_p. smt (@FieldR @IntDiv @Constants).
seq 1 0 : (#pre /\ a6c{1} = FieldR.asint ((statePowerOfAlpha6G * (proofLookupSPolyOpeningAtZOmegaG * stateBetaLookupG + stateGammaLookupG * (stateBetaLookupG + FieldR.one)) * proofLookupGrandProductOpeningAtZOmegaG) * (stateZG - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)))).
wp. skip. progress. 
rewrite Constants.r_eq_fieldr_p. smt (@FieldR @IntDiv @Constants).
seq 1 0 : (#pre /\ a7c{1} = FieldR.asint (statePowerOfAlpha7G * stateL0AtZG)).
wp. skip. progress. 
rewrite Constants.r_eq_fieldr_p. smt (@FieldR @IntDiv).
seq 1 0 : (#pre /\ betaGammaPowered{1} = FieldR.asint (stateGammaLookupG^(Constants.DOMAIN_SIZE - 1) * (stateBetaLookupG + FieldR.one)^(Constants.DOMAIN_SIZE - 1))).
inline*. wp. skip. progress. 
rewrite Constants.r_eq_fieldr_p. do rewrite Field.RexpE.
rewrite -FieldR.inFK.
rewrite FieldR.inF_exp.
have ->: 0 <= Constants.DOMAIN_SIZE - 1 by rewrite /Constants.DOMAIN_SIZE; progress.
simplify. smt (@FieldR @IntDiv).
seq 1 0 : (#pre /\ a8c{1} = FieldR.asint (statePowerOfAlpha8G * stateLnMinusOneAtZG * stateGammaLookupG^(Constants.DOMAIN_SIZE - 1) * (stateBetaLookupG + FieldR.one)^(Constants.DOMAIN_SIZE - 1))).
wp. skip. progress. 
rewrite Constants.r_eq_fieldr_p.
pose x := Field.(^) _ _.
pose x1 := Field.(^) _ _.

rewrite FieldR.mulE.
rewrite FieldR.mulE.
rewrite -modzMml.
rewrite -(modzMm (FieldR.asint (statePowerOfAlpha8{2} * stateLnMinusOneAtZ{2} * x)) (FieldR.asint x1)).
rewrite -(modzMm (FieldR.asint x) (FieldR.asint x1)).
rewrite -(modzMm (FieldR.asint statePowerOfAlpha8{2}) (FieldR.asint stateLnMinusOneAtZ{2})).
pose z1 := (FieldR.asint statePowerOfAlpha8{2}) %% FieldR.p.
pose z2 := (FieldR.asint stateLnMinusOneAtZ{2}) %% FieldR.p.
pose z3 := (z1 * z2) %% FieldR.p.
pose z4 := (FieldR.asint x) %% FieldR.p.
pose z5 := (FieldR.asint x1) %% FieldR.p.
pose z6 := (z4 * z5) %% FieldR.p.
pose z7 := (z3 * z6) %% FieldR.p.
rewrite -(modzMmr _ z5).
rewrite FieldR.mulE.
pose z8 := z5 %% FieldR.p.
rewrite -(modzMmr _ (FieldR.asint x)).
rewrite -/z4.
rewrite FieldR.mulE.
rewrite -(modzMm (FieldR.asint statePowerOfAlpha8{2})).
rewrite -/z1.
rewrite -/z2.
smt (@IntDiv @FieldR @Constants).
skip. progress.
smt (@IntDiv @FieldR @Constants).
qed.
