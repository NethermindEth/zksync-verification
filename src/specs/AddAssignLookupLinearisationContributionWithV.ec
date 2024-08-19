require        Constants.
require import Field.
require import IntDiv.
require import Memory.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

abbrev (+) = FieldR.(+).
abbrev [-] = FieldR.([-]).

module AddAssignLookupLinearisationContributionWithV = {
  proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256): unit = {
    var factor, _2, _3, _5, _9, _11, _13, fReconstructed, eta', currentEta, _15, _16, _18, _19, _21, _23, _25, _26, _27, _29, _31, _32, _34, _36, _37, _38;
    factor <@ Primops.mload(PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    _2 <@ Primops.mload(STATE_POWER_OF_ALPHA_6_SLOT);
    factor <- (PurePrimops.mulmod factor _2 R_MOD);
    _3 <@ Primops.mload(STATE_Z_MINUS_LAST_OMEGA_SLOT);
    factor <- (PurePrimops.mulmod factor _3 R_MOD);
    _5 <@ Primops.mload(STATE_V_SLOT);
    factor <- (PurePrimops.mulmod factor _5 R_MOD);
    Primops.mstore(LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF, factor);
    factor <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT);
    _9 <@ Primops.mload(STATE_BETA_LOOKUP_SLOT);
    factor <- (PurePrimops.mulmod factor _9 R_MOD);
    _11 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT);
    factor <- (PurePrimops.addmod factor _11 R_MOD);
    _13 <@ Primops.mload(STATE_BETA_GAMMA_PLUS_GAMMA_SLOT);
    factor <- (PurePrimops.addmod factor _13 R_MOD);
    fReconstructed <- stateOpening0AtZ;
    eta' <@ Primops.mload(STATE_ETA_SLOT);
    currentEta <- eta';
    _15 <- (PurePrimops.mulmod eta' stateOpening1AtZ R_MOD);
    fReconstructed <- (PurePrimops.addmod stateOpening0AtZ _15 R_MOD);
    currentEta <- (PurePrimops.mulmod eta' eta' R_MOD);
    _16 <- (PurePrimops.mulmod currentEta stateOpening2AtZ R_MOD);
    fReconstructed <- (PurePrimops.addmod fReconstructed _16 R_MOD);
    currentEta <- (PurePrimops.mulmod currentEta eta' R_MOD);
    _18 <@ Primops.mload(PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT);
    _19 <- (PurePrimops.mulmod _18 currentEta R_MOD);
    fReconstructed <- (PurePrimops.addmod fReconstructed _19 R_MOD);
    _21 <@ Primops.mload(PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT);
    fReconstructed <- (PurePrimops.mulmod fReconstructed _21 R_MOD);
    _23 <@ Primops.mload(STATE_GAMMA_LOOKUP_SLOT);
    fReconstructed <- (PurePrimops.addmod fReconstructed _23 R_MOD);
    factor <- (PurePrimops.mulmod factor fReconstructed R_MOD);
    _25 <@ Primops.mload(STATE_BETA_PLUS_ONE_SLOT);
    factor <- (PurePrimops.mulmod factor _25 R_MOD);
    factor <- (R_MOD - factor);
    _26 <@ Primops.mload(STATE_POWER_OF_ALPHA_6_SLOT);
    factor <- (PurePrimops.mulmod factor _26 R_MOD);
    _27 <@ Primops.mload(STATE_Z_MINUS_LAST_OMEGA_SLOT);
    factor <- (PurePrimops.mulmod factor _27 R_MOD);
    _29 <@ Primops.mload(STATE_POWER_OF_ALPHA_7_SLOT);
    _31 <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _32 <- (PurePrimops.mulmod _31 _29 R_MOD);
    factor <- (PurePrimops.addmod factor _32 R_MOD);
    _34 <@ Primops.mload(STATE_POWER_OF_ALPHA_8_SLOT);
    _36 <@ Primops.mload(STATE_L_N_MINUS_ONE_AT_Z_SLOT);
    _37 <- (PurePrimops.mulmod _36 _34 R_MOD);
    factor <- (PurePrimops.addmod factor _37 R_MOD);
    _38 <@ Primops.mload(STATE_V_SLOT);
    factor <- (PurePrimops.mulmod factor _38 R_MOD);
    Primops.mstore(LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF, factor);
  }

  proc low_no_reassignment(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256): unit = {
    var factor, factor1, factor2, factor3, factor4, factor5, factor6, factor7, factor8, factor9, factor10, factor11, factor12, factor13, factor14, factor15, _2, _3, _5, _9, _11, _13, fReconstructed, fReconstructed1, fReconstructed2, fReconstructed3, fReconstructed4, fReconstructed5, eta', currentEta, currentEta1, currentEta2, _15, _16, _18, _19, _21, _23, _25, _26, _27, _29, _31, _32, _34, _36, _37, _38;
    factor <@ Primops.mload(PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    _2 <@ Primops.mload(STATE_POWER_OF_ALPHA_6_SLOT);
    factor1 <- (PurePrimops.mulmod factor _2 R_MOD);
    _3 <@ Primops.mload(STATE_Z_MINUS_LAST_OMEGA_SLOT);
    factor2 <- (PurePrimops.mulmod factor1 _3 R_MOD);
    _5 <@ Primops.mload(STATE_V_SLOT);
    factor3 <- (PurePrimops.mulmod factor2 _5 R_MOD);
    Primops.mstore(LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF, factor3);
    factor4 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT);
    _9 <@ Primops.mload(STATE_BETA_LOOKUP_SLOT);
    factor5 <- (PurePrimops.mulmod factor4 _9 R_MOD);
    _11 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT);
    factor6 <- (PurePrimops.addmod factor5 _11 R_MOD);
    _13 <@ Primops.mload(STATE_BETA_GAMMA_PLUS_GAMMA_SLOT);
    factor7 <- (PurePrimops.addmod factor6 _13 R_MOD);
    fReconstructed <- stateOpening0AtZ;
    eta' <@ Primops.mload(STATE_ETA_SLOT);
    currentEta <- eta';
    _15 <- (PurePrimops.mulmod eta' stateOpening1AtZ R_MOD);
    fReconstructed1 <- (PurePrimops.addmod stateOpening0AtZ _15 R_MOD);
    currentEta1 <- (PurePrimops.mulmod eta' eta' R_MOD);
    _16 <- (PurePrimops.mulmod currentEta1 stateOpening2AtZ R_MOD);
    fReconstructed2 <- (PurePrimops.addmod fReconstructed1 _16 R_MOD);
    currentEta2 <- (PurePrimops.mulmod currentEta1 eta' R_MOD);
    _18 <@ Primops.mload(PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT);
    _19 <- (PurePrimops.mulmod _18 currentEta2 R_MOD);
    fReconstructed3 <- (PurePrimops.addmod fReconstructed2 _19 R_MOD);
    _21 <@ Primops.mload(PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT);
    fReconstructed4 <- (PurePrimops.mulmod fReconstructed3 _21 R_MOD);
    _23 <@ Primops.mload(STATE_GAMMA_LOOKUP_SLOT);
    fReconstructed5 <- (PurePrimops.addmod fReconstructed4 _23 R_MOD);
    factor8 <- (PurePrimops.mulmod factor7 fReconstructed5 R_MOD);
    _25 <@ Primops.mload(STATE_BETA_PLUS_ONE_SLOT);
    factor9 <- (PurePrimops.mulmod factor8 _25 R_MOD);
    factor10 <- (R_MOD - factor9);
    _26 <@ Primops.mload(STATE_POWER_OF_ALPHA_6_SLOT);
    factor11 <- (PurePrimops.mulmod factor10 _26 R_MOD);
    _27 <@ Primops.mload(STATE_Z_MINUS_LAST_OMEGA_SLOT);
    factor12 <- (PurePrimops.mulmod factor11 _27 R_MOD);
    _29 <@ Primops.mload(STATE_POWER_OF_ALPHA_7_SLOT);
    _31 <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _32 <- (PurePrimops.mulmod _31 _29 R_MOD);
    factor13 <- (PurePrimops.addmod factor12 _32 R_MOD);
    _34 <@ Primops.mload(STATE_POWER_OF_ALPHA_8_SLOT);
    _36 <@ Primops.mload(STATE_L_N_MINUS_ONE_AT_Z_SLOT);
    _37 <- (PurePrimops.mulmod _36 _34 R_MOD);
    factor14 <- (PurePrimops.addmod factor13 _37 R_MOD);
    _38 <@ Primops.mload(STATE_V_SLOT);
    factor15 <- (PurePrimops.mulmod factor14 _38 R_MOD);
    Primops.mstore(LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF, factor15);
  }

  proc low_no_reassignment_and_mstore(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256): uint256 * uint256 = {
    var factor, factor1, factor2, factor3, factor4, factor5, factor6, factor7, factor8, factor9, factor10, factor11, factor12, factor13, factor14, factor15, _2, _3, _5, _9, _11, _13, fReconstructed, fReconstructed1, fReconstructed2, fReconstructed3, fReconstructed4, fReconstructed5, eta', currentEta, currentEta1, currentEta2, _15, _16, _18, _19, _21, _23, _25, _26, _27, _29, _31, _32, _34, _36, _37, _38;
    factor <@ Primops.mload(PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    _2 <@ Primops.mload(STATE_POWER_OF_ALPHA_6_SLOT);
    factor1 <- (PurePrimops.mulmod factor _2 R_MOD);
    _3 <@ Primops.mload(STATE_Z_MINUS_LAST_OMEGA_SLOT);
    factor2 <- (PurePrimops.mulmod factor1 _3 R_MOD);
    _5 <@ Primops.mload(STATE_V_SLOT);
    factor3 <- (PurePrimops.mulmod factor2 _5 R_MOD);
    factor4 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT);
    _9 <@ Primops.mload(STATE_BETA_LOOKUP_SLOT);
    factor5 <- (PurePrimops.mulmod factor4 _9 R_MOD);
    _11 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT);
    factor6 <- (PurePrimops.addmod factor5 _11 R_MOD);
    _13 <@ Primops.mload(STATE_BETA_GAMMA_PLUS_GAMMA_SLOT);
    factor7 <- (PurePrimops.addmod factor6 _13 R_MOD);
    fReconstructed <- stateOpening0AtZ;
    eta' <@ Primops.mload(STATE_ETA_SLOT);
    currentEta <- eta';
    _15 <- (PurePrimops.mulmod eta' stateOpening1AtZ R_MOD);
    fReconstructed1 <- (PurePrimops.addmod stateOpening0AtZ _15 R_MOD);
    currentEta1 <- (PurePrimops.mulmod eta' eta' R_MOD);
    _16 <- (PurePrimops.mulmod currentEta1 stateOpening2AtZ R_MOD);
    fReconstructed2 <- (PurePrimops.addmod fReconstructed1 _16 R_MOD);
    currentEta2 <- (PurePrimops.mulmod currentEta1 eta' R_MOD);
    _18 <@ Primops.mload(PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT);
    _19 <- (PurePrimops.mulmod _18 currentEta2 R_MOD);
    fReconstructed3 <- (PurePrimops.addmod fReconstructed2 _19 R_MOD);
    _21 <@ Primops.mload(PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT);
    fReconstructed4 <- (PurePrimops.mulmod fReconstructed3 _21 R_MOD);
    _23 <@ Primops.mload(STATE_GAMMA_LOOKUP_SLOT);
    fReconstructed5 <- (PurePrimops.addmod fReconstructed4 _23 R_MOD);
    factor8 <- (PurePrimops.mulmod factor7 fReconstructed5 R_MOD);
    _25 <@ Primops.mload(STATE_BETA_PLUS_ONE_SLOT);
    factor9 <- (PurePrimops.mulmod factor8 _25 R_MOD);
    factor10 <- (R_MOD - factor9);
    _26 <@ Primops.mload(STATE_POWER_OF_ALPHA_6_SLOT);
    factor11 <- (PurePrimops.mulmod factor10 _26 R_MOD);
    _27 <@ Primops.mload(STATE_Z_MINUS_LAST_OMEGA_SLOT);
    factor12 <- (PurePrimops.mulmod factor11 _27 R_MOD);
    _29 <@ Primops.mload(STATE_POWER_OF_ALPHA_7_SLOT);
    _31 <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _32 <- (PurePrimops.mulmod _31 _29 R_MOD);
    factor13 <- (PurePrimops.addmod factor12 _32 R_MOD);
    _34 <@ Primops.mload(STATE_POWER_OF_ALPHA_8_SLOT);
    _36 <@ Primops.mload(STATE_L_N_MINUS_ONE_AT_Z_SLOT);
    _37 <- (PurePrimops.mulmod _36 _34 R_MOD);
    factor14 <- (PurePrimops.addmod factor13 _37 R_MOD);
    _38 <@ Primops.mload(STATE_V_SLOT);
    factor15 <- (PurePrimops.mulmod factor14 _38 R_MOD);
    return (factor3, factor15);
  }

  proc low'(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256): uint256 * uint256 = {
    var factor, factor1, factor2, factor3, factor4, factor5, factor6, factor7, factor8, factor9, factor10, factor11, factor12, factor13, factor14, factor15, _2, _3, _5, _9, _11, _13, fReconstructed, fReconstructed1, fReconstructed2, fReconstructed3, fReconstructed4, fReconstructed5, eta', currentEta, currentEta1, currentEta2, _15, _16, _18, _19, _21, _23, _25, _26, _27, _29, _31, _32, _34, _36, _37, _38;
    factor <@ Primops.mload(PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    _2 <@ Primops.mload(STATE_POWER_OF_ALPHA_6_SLOT);
    factor1 <- (PurePrimops.mulmod factor _2 R_MOD);
    _3 <@ Primops.mload(STATE_Z_MINUS_LAST_OMEGA_SLOT);
    factor2 <- (PurePrimops.mulmod factor1 _3 R_MOD);
    _5 <@ Primops.mload(STATE_V_SLOT);
    factor3 <- (PurePrimops.mulmod factor2 _5 R_MOD);
    factor4 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT);
    _9 <@ Primops.mload(STATE_BETA_LOOKUP_SLOT);
    factor5 <- (PurePrimops.mulmod factor4 _9 R_MOD);
    _11 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT);
    factor6 <- (PurePrimops.addmod factor5 _11 R_MOD);
    _13 <@ Primops.mload(STATE_BETA_GAMMA_PLUS_GAMMA_SLOT);
    factor7 <- (PurePrimops.addmod factor6 _13 R_MOD);
    fReconstructed <- stateOpening0AtZ;
    eta' <@ Primops.mload(STATE_ETA_SLOT);
    currentEta <- eta';
    _15 <- (PurePrimops.mulmod eta' stateOpening1AtZ R_MOD);
    fReconstructed1 <- (PurePrimops.addmod stateOpening0AtZ _15 R_MOD);
    currentEta1 <- (PurePrimops.mulmod eta' eta' R_MOD);
    _16 <- (PurePrimops.mulmod currentEta1 stateOpening2AtZ R_MOD);
    fReconstructed2 <- (PurePrimops.addmod fReconstructed1 _16 R_MOD);
    currentEta2 <- (PurePrimops.mulmod currentEta1 eta' R_MOD);
    _18 <@ Primops.mload(PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT);
    _19 <- (PurePrimops.mulmod _18 currentEta2 R_MOD);
    fReconstructed3 <- (PurePrimops.addmod fReconstructed2 _19 R_MOD);
    _21 <@ Primops.mload(PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT);
    fReconstructed4 <- (PurePrimops.mulmod fReconstructed3 _21 R_MOD);
    _23 <@ Primops.mload(STATE_GAMMA_LOOKUP_SLOT);
    fReconstructed5 <- (PurePrimops.addmod fReconstructed4 _23 R_MOD);
    factor8 <- (PurePrimops.mulmod factor7 fReconstructed5 R_MOD);
    _25 <@ Primops.mload(STATE_BETA_PLUS_ONE_SLOT);
    factor9 <- (PurePrimops.mulmod factor8 _25 R_MOD);
    factor10 <-W256.of_int ((- to_uint factor9) %% Constants.R);  
    _26 <@ Primops.mload(STATE_POWER_OF_ALPHA_6_SLOT);
    factor11 <- (PurePrimops.mulmod factor10 _26 R_MOD);
    _27 <@ Primops.mload(STATE_Z_MINUS_LAST_OMEGA_SLOT);
    factor12 <- (PurePrimops.mulmod factor11 _27 R_MOD);
    _29 <@ Primops.mload(STATE_POWER_OF_ALPHA_7_SLOT);
    _31 <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _32 <- (PurePrimops.mulmod _31 _29 R_MOD);
    factor13 <- (PurePrimops.addmod factor12 _32 R_MOD);
    _34 <@ Primops.mload(STATE_POWER_OF_ALPHA_8_SLOT);
    _36 <@ Primops.mload(STATE_L_N_MINUS_ONE_AT_Z_SLOT);
    _37 <- (PurePrimops.mulmod _36 _34 R_MOD);
    factor14 <- (PurePrimops.addmod factor13 _37 R_MOD);
    _38 <@ Primops.mload(STATE_V_SLOT);
    factor15 <- (PurePrimops.mulmod factor14 _38 R_MOD);
    return (factor3, factor15);
  }

  proc mid(stateOpening0AtZ : int, stateOpening1AtZ : int, stateOpening2AtZ : int,
           proofLookupGrandProductOpeningAtZOmega: int,
           powerOfAlpha6: int,
           zMinusLastOmega: int,
           v: int,
           proofLookupTPolyOpeningAtZOmega: int,
           betaLookup: int,
           proofLookupTPolyOpeningAtZ: int,
           betaGammaPlusGamma: int,
           eta': int,
           proofLookupTableTypePolyOpeningAtZ: int,
           proofLookupSelectorPolyOpeningAtZ: int,
           gammaLookup: int,
           betaPlusOne: int,
           powerOfAlpha7: int,
           l0AtZ: int,
           powerOfAlpha8: int,
           lNMinusOneAtZ: int
    ): int * int = {
    var lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient;
    lookupSFirstAggregatedCommitment <- (v * zMinusLastOmega * powerOfAlpha6 * proofLookupGrandProductOpeningAtZOmega) %% Constants.R;
    lookupGrandProductFirstAggregatedCoefficient 
            <- ((- (proofLookupTPolyOpeningAtZOmega * betaLookup +
            proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) *
            ((stateOpening0AtZ + eta' * stateOpening1AtZ +
              eta' * eta' * stateOpening2AtZ +
              eta' * eta' * eta' * proofLookupTableTypePolyOpeningAtZ) *
            proofLookupSelectorPolyOpeningAtZ + gammaLookup)) *
        betaPlusOne * powerOfAlpha6 * zMinusLastOmega + powerOfAlpha7 * l0AtZ +
        powerOfAlpha8 * lNMinusOneAtZ) *
          v %% Constants.R;
    return (lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient);
  }

  proc high(stateOpening0AtZ : FieldR.F, stateOpening1AtZ : FieldR.F, stateOpening2AtZ : FieldR.F,
           proofLookupGrandProductOpeningAtZOmega: FieldR.F,
           powerOfAlpha6: FieldR.F,
           zMinusLastOmega: FieldR.F,
           v: FieldR.F,
           proofLookupTPolyOpeningAtZOmega: FieldR.F,
           betaLookup: FieldR.F,
           proofLookupTPolyOpeningAtZ: FieldR.F,
           betaGammaPlusGamma: FieldR.F,
           eta': FieldR.F,
           proofLookupTableTypePolyOpeningAtZ: FieldR.F,
           proofLookupSelectorPolyOpeningAtZ: FieldR.F,
           gammaLookup: FieldR.F,
           betaPlusOne: FieldR.F,
           powerOfAlpha7: FieldR.F,
           l0AtZ: FieldR.F,
           powerOfAlpha8: FieldR.F,
           lNMinusOneAtZ: FieldR.F
    ): FieldR.F * FieldR.F = {
    var lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient;
    lookupSFirstAggregatedCommitment <- v * zMinusLastOmega * powerOfAlpha6 * proofLookupGrandProductOpeningAtZOmega;
    lookupGrandProductFirstAggregatedCoefficient 
            <- ((- (proofLookupTPolyOpeningAtZOmega * betaLookup +
            proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) *
            ((stateOpening0AtZ + eta' * stateOpening1AtZ +
              eta' * eta' * stateOpening2AtZ +
              eta' * eta' * eta' * proofLookupTableTypePolyOpeningAtZ) *
            proofLookupSelectorPolyOpeningAtZ + gammaLookup)) *
        betaPlusOne * powerOfAlpha6 * zMinusLastOmega + powerOfAlpha7 * l0AtZ +
        powerOfAlpha8 * lNMinusOneAtZ) *
          v;
    return (lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient);
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

lemma addAssignLookupLinearisationContributionWithV_low_equiv_low_no_reassignment:
    equiv [
      AddAssignLookupLinearisationContributionWithV.low ~ AddAssignLookupLinearisationContributionWithV.low_no_reassignment :
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

op addAssignLookupLinearisationContributionWithV_memory_footprint (mem_0: mem) (scratch1 scratch2): mem =
    let mem_1 = store mem_0 LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF scratch1 in
    store mem_1 LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF scratch2.

lemma addAssignLookupLinearisationContributionWithV_low_no_reassignment_equiv_low_no_reassignment_and_mstore (mem_0: mem):
    equiv [
      AddAssignLookupLinearisationContributionWithV.low_no_reassignment ~ AddAssignLookupLinearisationContributionWithV.low_no_reassignment_and_mstore :
      ={arg, glob AddAssignLookupLinearisationContributionWithV} /\
      Primops.memory{1} = mem_0 
      ==> 
      Primops.memory{1} = addAssignLookupLinearisationContributionWithV_memory_footprint mem_0 res{2}.`1 res{2}.`2 /\ 
      Primops.memory{2} = mem_0
    ].
proof.
  proc.
  seq 7 7 : (#pre /\ ={factor1, factor2, factor3}).
  inline*. sp. skip. progress.
  seq 1 0 : (={factor1, factor2, factor3} /\ ={dest, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ} /\ Primops.memory{2} = mem_0  /\ Primops.memory{1} = store mem_0 LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF factor3{1}).
  inline*. sp. skip. progress.
  rewrite /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /STATE_POWER_OF_ALPHA_6_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT
          /STATE_V_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /STATE_BETA_LOOKUP_SLOT
          /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT
          /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT
          /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_7_SLOT /STATE_L_0_AT_Z_SLOT /STATE_POWER_OF_ALPHA_8_SLOT /STATE_L_N_MINUS_ONE_AT_Z_SLOT
          /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFFLOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF.
  seq 41 41 : (={factor3, factor4, factor5, factor6, factor7, factor8, factor11, factor12, factor13, factor14, factor15, fReconstructed,
  fReconstructed1, fReconstructed2, fReconstructed3, fReconstructed4, currentEta, currentEta1, currentEta2} /\ Primops.memory{2} = mem_0 /\ Primops.memory{1} = store mem_0 LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF factor3{1}).
  inline*. sp. skip. progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /STATE_BETA_LOOKUP_SLOT load_store_diff; try by progress.
  rewrite load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT load_store_diff; try  by progress.
  rewrite load_store_diff; try by progress.
  rewrite load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_6_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_6_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_6_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT /STATE_L_0_AT_Z_SLOT /STATE_POWER_OF_ALPHA_7_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_6_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT /STATE_L_0_AT_Z_SLOT /STATE_POWER_OF_ALPHA_7_SLOT /STATE_L_N_MINUS_ONE_AT_Z_SLOT /STATE_POWER_OF_ALPHA_8_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_6_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT /STATE_L_0_AT_Z_SLOT /STATE_POWER_OF_ALPHA_7_SLOT /STATE_L_N_MINUS_ONE_AT_Z_SLOT /STATE_POWER_OF_ALPHA_8_SLOT /STATE_V_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_6_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT /STATE_L_0_AT_Z_SLOT /STATE_POWER_OF_ALPHA_7_SLOT /STATE_L_N_MINUS_ONE_AT_Z_SLOT /STATE_POWER_OF_ALPHA_8_SLOT /STATE_V_SLOT /STATE_ETA_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite /STATE_ETA_SLOT /LOOKUP_S_FIRST_AGGREAGETED_COMMITMENT_COEFF /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF.
  progress.
  rewrite /STATE_ETA_SLOT /LOOKUP_S_FIRST_AGGREAGETED_COMMITMENT_COEFF /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF.
  progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_6_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT /STATE_L_0_AT_Z_SLOT /STATE_POWER_OF_ALPHA_7_SLOT /STATE_L_N_MINUS_ONE_AT_Z_SLOT /STATE_POWER_OF_ALPHA_8_SLOT /STATE_V_SLOT /STATE_ETA_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_6_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT /STATE_L_0_AT_Z_SLOT /STATE_POWER_OF_ALPHA_7_SLOT /STATE_L_N_MINUS_ONE_AT_Z_SLOT /STATE_POWER_OF_ALPHA_8_SLOT /STATE_V_SLOT /STATE_ETA_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite load_store_diff; try by progress.
  rewrite /STATE_ETA_SLOT /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF.
  progress.
  rewrite /STATE_ETA_SLOT /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF.
  progress.
  rewrite /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT  /STATE_BETA_LOOKUP_SLOT /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /STATE_ETA_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /STATE_GAMMA_LOOKUP_SLOT /STATE_BETA_PLUS_ONE_SLOT /STATE_POWER_OF_ALPHA_6_SLOT /STATE_Z_MINUS_LAST_OMEGA_SLOT /STATE_L_0_AT_Z_SLOT /STATE_POWER_OF_ALPHA_7_SLOT /STATE_L_N_MINUS_ONE_AT_Z_SLOT /STATE_POWER_OF_ALPHA_8_SLOT /STATE_V_SLOT /STATE_ETA_SLOT load_store_diff; try  by progress.
  do! rewrite load_store_diff; try by progress.
  rewrite /STATE_ETA_SLOT /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF. progress.
  rewrite /STATE_ETA_SLOT /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF. progress.
  inline*. sp. skip. progress.
qed.

    
lemma addAssignLookupLinearisationContributionWithV_low_no_reassignment_and_mstore_equiv_low':
    equiv [
      AddAssignLookupLinearisationContributionWithV.low_no_reassignment_and_mstore ~ AddAssignLookupLinearisationContributionWithV.low' :
      ={arg, glob AddAssignLookupLinearisationContributionWithV} ==>
      ={res, glob AddAssignLookupLinearisationContributionWithV}
    ].
proof.
  proc.
  seq 33 33: (#pre /\ ={factor1, factor2, factor3, factor4, factor5, factor6, factor7, factor8, factor9} /\ factor9{1} < R_MOD).
  inline*. sp. skip. progress.
  have H_mulmod: forall (x y: uint256), PurePrimops.mulmod x y R_MOD < R_MOD. rewrite /mulmod. progress. rewrite Utils.uint256_lt_of_lt. rewrite W256.of_uintK. by smt(@W256 @Utils).
  rewrite H_mulmod.
   seq 3 3 : (#pre /\ ={factor11}).
  inline*. sp. skip. progress.
  rewrite /mulmod /addmod. simplify.
  case (factor9{2} = W256.zero).
  progress. progress.
  have -> : R_MOD - W256.zero = R_MOD by smt(@W256).
  have H_mul: forall(a b c: int), (a %% b * c) %% b = (a * c) %% b by smt (@IntDiv).
  rewrite -H_mul. smt (@W256 @Utils @IntDiv). 
  have H_mul: forall(b a c: int), (a %% b * c) %% b = (a * c) %% b by smt (@IntDiv).
  have H_add: forall (b a c: int),  (a %% b + c) %% b = (a + c) %% b by smt(@IntDiv).
  rewrite -(H_mul (to_uint R_MOD)).
  progress.
  have -> : (W256.to_uint (R_MOD - factor9{2})) %% W256.to_uint R_MOD = (to_uint (of_int ((- to_uint factor9{2}) %% Constants.R)))%W256.
  do rewrite W256.of_uintK. rewrite -/Constants.R -/R_MOD.
  rewrite Utils.mod_R_W256_mod_R.
  rewrite Utils.uint256_to_uint_sub_eq_sub_to_uint. smt().
  rewrite -H_add.
  have -> : W256.to_uint R_MOD %% Constants.R = 0 by smt(@W256 @Utils @Constants).
  by reflexivity.
  by reflexivity.
  inline*. sp. by progress.
qed.

    
lemma addAssignLookupLinearisationContributionWithV_low_no_reassignment_and_mstore_equiv_mid
  (low_dest low_stateOpening0AtZ low_stateOpening1AtZ low_stateOpening2AtZ: uint256)
    (mid_stateOpening0AtZ mid_stateOpening1AtZ mid_stateOpening2AtZ
           proofLookupGrandProductOpeningAtZOmega
           powerOfAlpha6
           zMinusLastOmega
           v
           proofLookupTPolyOpeningAtZOmega
           betaLookup
           proofLookupTPolyOpeningAtZ
           betaGammaPlusGamma
           eta_L
           proofLookupTableTypePolyOpeningAtZ
           proofLookupSelectorPolyOpeningAtZ
           gammaLookup
           betaPlusOne
           powerOfAlpha7
           l0AtZ
           powerOfAlpha8
           lNMinusOneAtZ: int
    ):
    equiv [
      AddAssignLookupLinearisationContributionWithV.low' ~ AddAssignLookupLinearisationContributionWithV.mid: 
      arg{1} = (low_dest, low_stateOpening0AtZ, low_stateOpening1AtZ, low_stateOpening2AtZ) /\
      arg{2} = (mid_stateOpening0AtZ, mid_stateOpening1AtZ, mid_stateOpening2AtZ,
           proofLookupGrandProductOpeningAtZOmega,
           powerOfAlpha6,
           zMinusLastOmega,
           v,
           proofLookupTPolyOpeningAtZOmega,
           betaLookup,
           proofLookupTPolyOpeningAtZ,
           betaGammaPlusGamma,
           eta_L,
           proofLookupTableTypePolyOpeningAtZ,
           proofLookupSelectorPolyOpeningAtZ,
           gammaLookup,
           betaPlusOne,
           powerOfAlpha7,
           l0AtZ,
           powerOfAlpha8,
           lNMinusOneAtZ) /\
      W256.to_uint low_stateOpening0AtZ = mid_stateOpening0AtZ /\
      W256.to_uint low_stateOpening1AtZ = mid_stateOpening1AtZ /\
      W256.to_uint low_stateOpening2AtZ = mid_stateOpening2AtZ /\
      0 <= mid_stateOpening0AtZ < Constants.R /\
      0 <= mid_stateOpening1AtZ < Constants.R /\
      0 <= mid_stateOpening2AtZ < Constants.R /\
      0 <= proofLookupGrandProductOpeningAtZOmega < Constants.R /\
      0 <= powerOfAlpha6 < Constants.R /\
      0 <= zMinusLastOmega < Constants.R /\
      0 <= v < Constants.R /\
      0 <= proofLookupTPolyOpeningAtZOmega < Constants.R /\
      0 <= betaLookup < Constants.R /\
      0 <= betaGammaPlusGamma < Constants.R /\
      0 <= eta_L < Constants.R /\
      0 <= proofLookupTableTypePolyOpeningAtZ < Constants.R /\
      0 <= proofLookupSelectorPolyOpeningAtZ < Constants.R /\
      0 <= gammaLookup < Constants.R /\
      0 <= betaPlusOne < Constants.R /\
      0 <= powerOfAlpha7 < Constants.R /\
      0 <= l0AtZ < Constants.R /\
      0 <= powerOfAlpha8 < Constants.R /\
      0 <= lNMinusOneAtZ < Constants.R /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmega /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_6_SLOT) = powerOfAlpha6 /\
      W256.to_uint (load Primops.memory{1} STATE_Z_MINUS_LAST_OMEGA_SLOT) = zMinusLastOmega /\
      W256.to_uint (load Primops.memory{1} STATE_V_SLOT) = v /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupTPolyOpeningAtZOmega /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_LOOKUP_SLOT) = betaLookup /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) = proofLookupTPolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) = betaGammaPlusGamma /\
      W256.to_uint (load Primops.memory{1} STATE_ETA_SLOT) = eta_L /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) = proofLookupTableTypePolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) = proofLookupSelectorPolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} STATE_GAMMA_LOOKUP_SLOT) = gammaLookup /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_PLUS_ONE_SLOT) = betaPlusOne /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_7_SLOT) = powerOfAlpha7 /\
      W256.to_uint (load Primops.memory{1} STATE_L_0_AT_Z_SLOT) = l0AtZ /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_8_SLOT) = powerOfAlpha8 /\
      W256.to_uint (load Primops.memory{1} STATE_L_N_MINUS_ONE_AT_Z_SLOT) = lNMinusOneAtZ
      ==>
      W256.to_uint res{1}.`1 = res{2}.`1 /\
      W256.to_uint res{1}.`2 = res{2}.`2 
    ].
proof.
  have H_add: forall (a b c: int),  (a %% b + c) %% b = (a + c) %% b by smt(@IntDiv).
    have H_add': forall (a b c: int),  (a + c %% b) %% b = (a + c) %% b by smt(@IntDiv).
  have H_mul: forall(a b c: int), (a %% b * c) %% b = (a * c) %% b by smt (@IntDiv).
  proc.
  sp.
  inline *.
  seq 4 0 : (#pre /\ W256.to_uint factor{1} = proofLookupGrandProductOpeningAtZOmega
             /\ W256.to_uint _2{1} = powerOfAlpha6).
  sp. skip. progress.
  seq 1 0 : (#pre /\ W256.to_uint factor1{1} = (proofLookupGrandProductOpeningAtZOmega * powerOfAlpha6) %% Constants.R).
  sp. skip.  progress.
  rewrite /mulmod H37 H38.  smt (@W256 @Utils).
  seq 3 0: (#pre /\ W256.to_uint _3{1} = zMinusLastOmega /\ W256.to_uint factor2{1} = (proofLookupGrandProductOpeningAtZOmega * powerOfAlpha6 * zMinusLastOmega) %% Constants.R).
  sp. skip. progress.
  rewrite /mulmod H39. simplify. smt (@W256 @Utils @IntDiv).
  seq 3 1: (#pre /\ W256.to_uint _5{1} = v /\ W256.to_uint factor3{1} = (proofLookupGrandProductOpeningAtZOmega * powerOfAlpha6 * zMinusLastOmega * v) %% Constants.R /\ lookupSFirstAggregatedCommitment{2} = W256.to_uint factor3{1}).
  sp. skip. progress.
  rewrite /mulmod H41.
  simplify. do rewrite W256.of_uintK. rewrite - /Constants.R. rewrite Utils.mod_R_W256_mod_R.
  rewrite H_mul. by reflexivity.
  rewrite /mulmod H41.
  simplify. rewrite W256.of_uintK.  rewrite /R_MOD /Constants.R -/Constants.R. rewrite W256.of_uintK. rewrite Utils.R_mod_W256_R.  rewrite Utils.mod_R_W256_mod_R. rewrite H_mul. smt (@W256 @Utils @IntDiv).
  seq 2 0: (#pre /\ W256.to_uint factor4{1} = proofLookupTPolyOpeningAtZOmega).
  sp. skip. progress.
  seq 3 0: (#pre /\ W256.to_uint factor5{1} = proofLookupTPolyOpeningAtZOmega * betaLookup %% Constants.R).  
  sp. skip. progress.
  rewrite /mulmod H45. smt (@W256 @Utils).
  seq 3 0: (#pre /\ W256.to_uint factor6{1} = (proofLookupTPolyOpeningAtZOmega * betaLookup + proofLookupTPolyOpeningAtZ) %% Constants.R).
  sp. skip. progress.
  rewrite /addmod H46.
  do rewrite W256.of_uintK. rewrite - /Constants.R. simplify. rewrite H_add. smt(@W256 @Utils @IntDiv).
  seq 3 0: (#pre /\ W256.to_uint factor7{1} = (proofLookupTPolyOpeningAtZOmega * betaLookup + proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) %% Constants.R).
  sp. skip. progress.
  rewrite /addmod H47.
  do rewrite W256.of_uintK. rewrite - /Constants.R. progress. rewrite W256.of_uintK.  smt(@W256 @Utils @IntDiv).
  seq 4 0: (#pre /\ fReconstructed{1} = stateOpening0AtZ{1} /\ W256.to_uint eta'{1} = eta_L /\ W256.to_uint currentEta{1} = eta_L).
  sp. skip. progress.
  seq 2 0: (#pre /\ W256.to_uint fReconstructed1{1} = (mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ) %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify. do rewrite W256.of_uintK. rewrite - /Constants.R. do rewrite Utils.mod_R_W256_mod_R. rewrite H_add'. smt (@W256 @Utils @IntDiv).
  seq 1 0: (#pre /\ W256.to_uint currentEta1{1} = (eta_L * eta_L) %% Constants.R).
  sp. skip. progress.
  rewrite /mulmod. simplify. rewrite W256.of_uintK H49. rewrite /Constants.R /R_MOD.  smt (@W256 @Utils @IntDiv).
  seq 2 0: (#pre /\ W256.to_uint fReconstructed2{1} = (mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ) %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod.
  progress. do rewrite W256.of_uintK. rewrite - /Constants.R H51 H52 H_add Utils.mod_R_W256_mod_R H_mul. rewrite Utils.mod_R_W256_mod_R. smt(@W256 @Utils @IntDiv).  
  seq 1 0: (#pre /\ W256.to_uint currentEta2{1} = (eta_L * eta_L * eta_L) %% Constants.R).
  sp. skip. progress.
  rewrite /mulmod. simplify. rewrite W256.of_uintK H49. rewrite /Constants.R /R_MOD. rewrite W256.of_uintK -/Constants.R Utils.mod_R_W256_mod_R H52. smt (@W256 @Utils @IntDiv).
  seq 4 0: (#pre /\ W256.to_uint fReconstructed3{1} = (mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify. rewrite W256.of_uintK H53 H54. rewrite /Constants.R /R_MOD. do rewrite W256.of_uintK - /Constants.R.
  do rewrite Utils.R_mod_W256_R. do rewrite Utils.mod_R_W256_mod_R.
  smt (@W256 @Utils @IntDiv).
  seq 3 0: (#pre /\ W256.to_uint fReconstructed4{1} = (mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) * proofLookupSelectorPolyOpeningAtZ %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify. rewrite W256.of_uintK H55. rewrite /Constants.R /R_MOD. do rewrite W256.of_uintK - /Constants.R.
  rewrite H_mul. do rewrite Utils.mod_R_W256_mod_R. by reflexivity.
  seq 3 0: (#pre /\ W256.to_uint fReconstructed5{1} = ((mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) * proofLookupSelectorPolyOpeningAtZ + gammaLookup)%% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod W256.of_uintK H56 /Constants.R /R_MOD - /Constants.R.
  simplify. do rewrite W256.of_uintK.
  rewrite Utils.mod_R_W256_mod_R.
  smt (@W256 @Utils @IntDiv).
  seq 1 0: (#pre /\ W256.to_uint factor8{1} = ((proofLookupTPolyOpeningAtZOmega * betaLookup + proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) * ((mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) * proofLookupSelectorPolyOpeningAtZ + gammaLookup)) %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify. rewrite W256.of_uintK H57. rewrite /Constants.R /R_MOD. do rewrite W256.of_uintK - /Constants.R.
  rewrite Utils.mod_R_W256_mod_R. rewrite H48.  smt (@W256 @Utils @IntDiv).
  seq 3 0: (#pre /\ W256.to_uint factor9{1} = ((proofLookupTPolyOpeningAtZOmega * betaLookup + proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) * ((mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) * proofLookupSelectorPolyOpeningAtZ + gammaLookup)) * betaPlusOne %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify. rewrite W256.of_uintK H58. rewrite /Constants.R /R_MOD. do rewrite W256.of_uintK - /Constants.R.
  rewrite Utils.mod_R_W256_mod_R. smt (@W256 @Utils @IntDiv).
  seq 1 0: (#pre /\ W256.to_uint factor10{1} = (-(proofLookupTPolyOpeningAtZOmega * betaLookup + proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) * ((mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) * proofLookupSelectorPolyOpeningAtZ + gammaLookup)) * betaPlusOne %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify.
  rewrite H59 W256.of_uintK Utils.mod_R_W256_mod_R.
  by smt().
  seq 3 0: (#pre /\ W256.to_uint factor11{1} = (-(proofLookupTPolyOpeningAtZOmega * betaLookup + proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) * ((mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) * proofLookupSelectorPolyOpeningAtZ + gammaLookup)) * betaPlusOne *powerOfAlpha6 %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify. rewrite W256.of_uintK H60. rewrite /Constants.R /R_MOD. do rewrite W256.of_uintK - /Constants.R.
  simplify. 
  rewrite Utils.mod_R_W256_mod_R.
  smt (@W256 @Utils @IntDiv).
  seq 3 0: (#pre /\ W256.to_uint factor12{1} = (-(proofLookupTPolyOpeningAtZOmega * betaLookup + proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) * ((mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) * proofLookupSelectorPolyOpeningAtZ + gammaLookup)) * betaPlusOne * powerOfAlpha6 * zMinusLastOmega %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify. rewrite H61. rewrite /Constants.R /R_MOD. rewrite - /Constants.R.
  simplify.
  do rewrite W256.of_uintK.
  rewrite -/Constants.R -/R_MOD.
  rewrite Utils.R_mod_W256_R.
  rewrite H_mul.
  smt (@W256 @Utils @IntDiv).
  seq 6 0: (#pre /\ W256.to_uint factor13{1} = ((-(proofLookupTPolyOpeningAtZOmega * betaLookup + proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) * ((mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) * proofLookupSelectorPolyOpeningAtZ + gammaLookup)) * betaPlusOne * powerOfAlpha6 * zMinusLastOmega + powerOfAlpha7 * l0AtZ) %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify. rewrite H62. rewrite /Constants.R /R_MOD. rewrite - /Constants.R.
  simplify.
  do rewrite W256.of_uintK.
  rewrite -/Constants.R -/R_MOD.
  rewrite Utils.R_mod_W256_R.
  rewrite Utils.mod_R_W256_mod_R.
  rewrite Utils.mod_R_W256_mod_R.
  rewrite H_add.
  smt (@W256 @Utils @IntDiv).
  seq 6 0 : (#pre /\ W256.to_uint factor14{1} = ((-(proofLookupTPolyOpeningAtZOmega * betaLookup + proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) * ((mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) * proofLookupSelectorPolyOpeningAtZ + gammaLookup)) * betaPlusOne * powerOfAlpha6 * zMinusLastOmega + powerOfAlpha7 * l0AtZ + powerOfAlpha8 * lNMinusOneAtZ) %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify. rewrite H63. rewrite /Constants.R /R_MOD. rewrite - /Constants.R.
  simplify.
  do rewrite W256.of_uintK.
  rewrite -/Constants.R -/R_MOD.
  rewrite Utils.R_mod_W256_R.
  rewrite Utils.mod_R_W256_mod_R.
  rewrite Utils.mod_R_W256_mod_R.
  smt (@W256 @Utils @IntDiv).
  seq 3 0 : (#pre /\ W256.to_uint factor15{1} = ((-(proofLookupTPolyOpeningAtZOmega * betaLookup + proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) * ((mid_stateOpening0AtZ + eta_L * mid_stateOpening1AtZ + eta_L * eta_L * mid_stateOpening2AtZ + eta_L * eta_L * eta_L * proofLookupTableTypePolyOpeningAtZ) * proofLookupSelectorPolyOpeningAtZ + gammaLookup)) * betaPlusOne * powerOfAlpha6 * zMinusLastOmega + powerOfAlpha7 * l0AtZ + powerOfAlpha8 * lNMinusOneAtZ) * v %% Constants.R).
  sp. skip. progress.
  rewrite /addmod /mulmod. simplify. rewrite H64. rewrite /Constants.R /R_MOD. rewrite - /Constants.R.
  simplify.
  do rewrite W256.of_uintK.
  rewrite -/Constants.R -/R_MOD.
  rewrite Utils.R_mod_W256_R.
  rewrite Utils.mod_R_W256_mod_R.
  smt (@W256 @Utils @IntDiv).
  skip.
  progress.
  rewrite H43.
  smt (@W256 @Utils @IntDiv @Int).
qed.

lemma addAssignLookupLinearisationContributionWithV_low_equiv_mid
    (mem_0: mem)
    (low_dest low_stateOpening0AtZ low_stateOpening1AtZ low_stateOpening2AtZ: uint256)
    (mid_stateOpening0AtZ mid_stateOpening1AtZ mid_stateOpening2AtZ
           proofLookupGrandProductOpeningAtZOmega
           powerOfAlpha6
           zMinusLastOmega
           v
           proofLookupTPolyOpeningAtZOmega
           betaLookup
           proofLookupTPolyOpeningAtZ
           betaGammaPlusGamma
           eta_L
           proofLookupTableTypePolyOpeningAtZ
           proofLookupSelectorPolyOpeningAtZ
           gammaLookup
           betaPlusOne
           powerOfAlpha7
           l0AtZ
           powerOfAlpha8
           lNMinusOneAtZ: int
    ):
    equiv [
      AddAssignLookupLinearisationContributionWithV.low ~ AddAssignLookupLinearisationContributionWithV.mid:
      Primops.memory{1} = mem_0 /\
      arg{1} = (low_dest, low_stateOpening0AtZ, low_stateOpening1AtZ, low_stateOpening2AtZ) /\
      arg{2} = (mid_stateOpening0AtZ, mid_stateOpening1AtZ, mid_stateOpening2AtZ,
           proofLookupGrandProductOpeningAtZOmega,
           powerOfAlpha6,
           zMinusLastOmega,
           v,
           proofLookupTPolyOpeningAtZOmega,
           betaLookup,
           proofLookupTPolyOpeningAtZ,
           betaGammaPlusGamma,
           eta_L,
           proofLookupTableTypePolyOpeningAtZ,
           proofLookupSelectorPolyOpeningAtZ,
           gammaLookup,
           betaPlusOne,
           powerOfAlpha7,
           l0AtZ,
           powerOfAlpha8,
           lNMinusOneAtZ) /\
      W256.to_uint low_stateOpening0AtZ = mid_stateOpening0AtZ /\
      W256.to_uint low_stateOpening1AtZ = mid_stateOpening1AtZ /\
      W256.to_uint low_stateOpening2AtZ = mid_stateOpening2AtZ /\
      0 <= mid_stateOpening0AtZ < Constants.R /\
      0 <= mid_stateOpening1AtZ < Constants.R /\
      0 <= mid_stateOpening2AtZ < Constants.R /\
      0 <= proofLookupGrandProductOpeningAtZOmega < Constants.R /\
      0 <= powerOfAlpha6 < Constants.R /\
      0 <= zMinusLastOmega < Constants.R /\
      0 <= v < Constants.R /\
      0 <= proofLookupTPolyOpeningAtZOmega < Constants.R /\
      0 <= betaLookup < Constants.R /\
      0 <= betaGammaPlusGamma < Constants.R /\
      0 <= eta_L < Constants.R /\
      0 <= proofLookupTableTypePolyOpeningAtZ < Constants.R /\
      0 <= proofLookupSelectorPolyOpeningAtZ < Constants.R /\
      0 <= gammaLookup < Constants.R /\
      0 <= betaPlusOne < Constants.R /\
      0 <= powerOfAlpha7 < Constants.R /\
      0 <= l0AtZ < Constants.R /\
      0 <= powerOfAlpha8 < Constants.R /\
      0 <= lNMinusOneAtZ < Constants.R /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmega /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_6_SLOT) = powerOfAlpha6 /\
      W256.to_uint (load Primops.memory{1} STATE_Z_MINUS_LAST_OMEGA_SLOT) = zMinusLastOmega /\
      W256.to_uint (load Primops.memory{1} STATE_V_SLOT) = v /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupTPolyOpeningAtZOmega /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_LOOKUP_SLOT) = betaLookup /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) = proofLookupTPolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) = betaGammaPlusGamma /\
      W256.to_uint (load Primops.memory{1} STATE_ETA_SLOT) = eta_L /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) = proofLookupTableTypePolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) = proofLookupSelectorPolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} STATE_GAMMA_LOOKUP_SLOT) = gammaLookup /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_PLUS_ONE_SLOT) = betaPlusOne /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_7_SLOT) = powerOfAlpha7 /\
      W256.to_uint (load Primops.memory{1} STATE_L_0_AT_Z_SLOT) = l0AtZ /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_8_SLOT) = powerOfAlpha8 /\
      W256.to_uint (load Primops.memory{1} STATE_L_N_MINUS_ONE_AT_Z_SLOT) = lNMinusOneAtZ
      ==>
      Primops.memory{1} = addAssignLookupLinearisationContributionWithV_memory_footprint mem_0 (W256.of_int res{2}.`1) (W256.of_int res{2}.`2)
    ].
proof. 
  transitivity AddAssignLookupLinearisationContributionWithV.low_no_reassignment
    (
      ={arg, glob AddAssignLookupLinearisationContributionWithV} /\ Primops.memory{1} = mem_0 ==>
      ={res, glob AddAssignLookupLinearisationContributionWithV}) 
    (Primops.memory{1} = mem_0 /\ arg{1} = (low_dest, low_stateOpening0AtZ, low_stateOpening1AtZ, low_stateOpening2AtZ) /\
      arg{2} = (mid_stateOpening0AtZ, mid_stateOpening1AtZ, mid_stateOpening2AtZ,
           proofLookupGrandProductOpeningAtZOmega,
           powerOfAlpha6,
           zMinusLastOmega,
           v,
           proofLookupTPolyOpeningAtZOmega,
           betaLookup,
           proofLookupTPolyOpeningAtZ,
           betaGammaPlusGamma,
           eta_L,
           proofLookupTableTypePolyOpeningAtZ,
           proofLookupSelectorPolyOpeningAtZ,
           gammaLookup,
           betaPlusOne,
           powerOfAlpha7,
           l0AtZ,
           powerOfAlpha8,
           lNMinusOneAtZ) /\
      W256.to_uint low_stateOpening0AtZ = mid_stateOpening0AtZ /\
      W256.to_uint low_stateOpening1AtZ = mid_stateOpening1AtZ /\
      W256.to_uint low_stateOpening2AtZ = mid_stateOpening2AtZ /\
      0 <= mid_stateOpening0AtZ < Constants.R /\
      0 <= mid_stateOpening1AtZ < Constants.R /\
      0 <= mid_stateOpening2AtZ < Constants.R /\
      0 <= proofLookupGrandProductOpeningAtZOmega < Constants.R /\
      0 <= powerOfAlpha6 < Constants.R /\
      0 <= zMinusLastOmega < Constants.R /\
      0 <= v < Constants.R /\
      0 <= proofLookupTPolyOpeningAtZOmega < Constants.R /\
      0 <= betaLookup < Constants.R /\
      0 <= betaGammaPlusGamma < Constants.R /\
      0 <= eta_L < Constants.R /\
      0 <= proofLookupTableTypePolyOpeningAtZ < Constants.R /\
      0 <= proofLookupSelectorPolyOpeningAtZ < Constants.R /\
      0 <= gammaLookup < Constants.R /\
      0 <= betaPlusOne < Constants.R /\
      0 <= powerOfAlpha7 < Constants.R /\
      0 <= l0AtZ < Constants.R /\
      0 <= powerOfAlpha8 < Constants.R /\
      0 <= lNMinusOneAtZ < Constants.R /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmega /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_6_SLOT) = powerOfAlpha6 /\
      W256.to_uint (load Primops.memory{1} STATE_Z_MINUS_LAST_OMEGA_SLOT) = zMinusLastOmega /\
      W256.to_uint (load Primops.memory{1} STATE_V_SLOT) = v /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupTPolyOpeningAtZOmega /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_LOOKUP_SLOT) = betaLookup /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) = proofLookupTPolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) = betaGammaPlusGamma /\
      W256.to_uint (load Primops.memory{1} STATE_ETA_SLOT) = eta_L /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) = proofLookupTableTypePolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) = proofLookupSelectorPolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} STATE_GAMMA_LOOKUP_SLOT) = gammaLookup /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_PLUS_ONE_SLOT) = betaPlusOne /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_7_SLOT) = powerOfAlpha7 /\
      W256.to_uint (load Primops.memory{1} STATE_L_0_AT_Z_SLOT) = l0AtZ /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_8_SLOT) = powerOfAlpha8 /\
      W256.to_uint (load Primops.memory{1} STATE_L_N_MINUS_ONE_AT_Z_SLOT) = lNMinusOneAtZ
      ==>
        Primops.memory{1} = addAssignLookupLinearisationContributionWithV_memory_footprint mem_0 (W256.of_int res{2}.`1) (W256.of_int res{2}.`2)).
        progress. by smt().
        by progress.
        progress.
        conseq (_ : ={arg, Primops.memory} ==> ={Primops.memory}).
        by progress.
    exact addAssignLookupLinearisationContributionWithV_low_equiv_low_no_reassignment.
  transitivity AddAssignLookupLinearisationContributionWithV.low_no_reassignment_and_mstore
    (
      ={arg, glob AddAssignLookupLinearisationContributionWithV} /\ Primops.memory{1} = mem_0
      ==> 
      Primops.memory{1} = addAssignLookupLinearisationContributionWithV_memory_footprint mem_0 res{2}.`1 res{2}.`2 /\ 
        Primops.memory{2} = mem_0)
    (arg{1} = (low_dest, low_stateOpening0AtZ, low_stateOpening1AtZ, low_stateOpening2AtZ) /\
      arg{2} = (mid_stateOpening0AtZ, mid_stateOpening1AtZ, mid_stateOpening2AtZ,
           proofLookupGrandProductOpeningAtZOmega,
           powerOfAlpha6,
           zMinusLastOmega,
           v,
           proofLookupTPolyOpeningAtZOmega,
           betaLookup,
           proofLookupTPolyOpeningAtZ,
           betaGammaPlusGamma,
           eta_L,
           proofLookupTableTypePolyOpeningAtZ,
           proofLookupSelectorPolyOpeningAtZ,
           gammaLookup,
           betaPlusOne,
           powerOfAlpha7,
           l0AtZ,
           powerOfAlpha8,
           lNMinusOneAtZ) /\
      W256.to_uint low_stateOpening0AtZ = mid_stateOpening0AtZ /\
      W256.to_uint low_stateOpening1AtZ = mid_stateOpening1AtZ /\
      W256.to_uint low_stateOpening2AtZ = mid_stateOpening2AtZ /\
      0 <= mid_stateOpening0AtZ < Constants.R /\
      0 <= mid_stateOpening1AtZ < Constants.R /\
      0 <= mid_stateOpening2AtZ < Constants.R /\
      0 <= proofLookupGrandProductOpeningAtZOmega < Constants.R /\
      0 <= powerOfAlpha6 < Constants.R /\
      0 <= zMinusLastOmega < Constants.R /\
      0 <= v < Constants.R /\
      0 <= proofLookupTPolyOpeningAtZOmega < Constants.R /\
      0 <= betaLookup < Constants.R /\
      0 <= betaGammaPlusGamma < Constants.R /\
      0 <= eta_L < Constants.R /\
      0 <= proofLookupTableTypePolyOpeningAtZ < Constants.R /\
      0 <= proofLookupSelectorPolyOpeningAtZ < Constants.R /\
      0 <= gammaLookup < Constants.R /\
      0 <= betaPlusOne < Constants.R /\
      0 <= powerOfAlpha7 < Constants.R /\
      0 <= l0AtZ < Constants.R /\
      0 <= powerOfAlpha8 < Constants.R /\
      0 <= lNMinusOneAtZ < Constants.R /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmega /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_6_SLOT) = powerOfAlpha6 /\
      W256.to_uint (load Primops.memory{1} STATE_Z_MINUS_LAST_OMEGA_SLOT) = zMinusLastOmega /\
      W256.to_uint (load Primops.memory{1} STATE_V_SLOT) = v /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupTPolyOpeningAtZOmega /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_LOOKUP_SLOT) = betaLookup /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) = proofLookupTPolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) = betaGammaPlusGamma /\
      W256.to_uint (load Primops.memory{1} STATE_ETA_SLOT) = eta_L /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) = proofLookupTableTypePolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) = proofLookupSelectorPolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} STATE_GAMMA_LOOKUP_SLOT) = gammaLookup /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_PLUS_ONE_SLOT) = betaPlusOne /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_7_SLOT) = powerOfAlpha7 /\
      W256.to_uint (load Primops.memory{1} STATE_L_0_AT_Z_SLOT) = l0AtZ /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_8_SLOT) = powerOfAlpha8 /\
      W256.to_uint (load Primops.memory{1} STATE_L_N_MINUS_ONE_AT_Z_SLOT) = lNMinusOneAtZ
      ==>
      W256.to_uint res{1}.`1 = res{2}.`1 /\
      W256.to_uint res{1}.`2 = res{2}.`2 ).
        progress.
        by smt().
    progress. rewrite -H -H0. do rewrite W256.to_uintK.
        by reflexivity.
    exact addAssignLookupLinearisationContributionWithV_low_no_reassignment_equiv_low_no_reassignment_and_mstore.
    transitivity AddAssignLookupLinearisationContributionWithV.low'
      (={arg, glob AddAssignLookupLinearisationContributionWithV} ==> ={res, glob AddAssignLookupLinearisationContributionWithV})
      (arg{1} = (low_dest, low_stateOpening0AtZ, low_stateOpening1AtZ, low_stateOpening2AtZ) /\
      arg{2} = (mid_stateOpening0AtZ, mid_stateOpening1AtZ, mid_stateOpening2AtZ,
           proofLookupGrandProductOpeningAtZOmega,
           powerOfAlpha6,
           zMinusLastOmega,
           v,
           proofLookupTPolyOpeningAtZOmega,
           betaLookup,
           proofLookupTPolyOpeningAtZ,
           betaGammaPlusGamma,
           eta_L,
           proofLookupTableTypePolyOpeningAtZ,
           proofLookupSelectorPolyOpeningAtZ,
           gammaLookup,
           betaPlusOne,
           powerOfAlpha7,
           l0AtZ,
           powerOfAlpha8,
           lNMinusOneAtZ) /\
      W256.to_uint low_stateOpening0AtZ = mid_stateOpening0AtZ /\
      W256.to_uint low_stateOpening1AtZ = mid_stateOpening1AtZ /\
      W256.to_uint low_stateOpening2AtZ = mid_stateOpening2AtZ /\
      0 <= mid_stateOpening0AtZ < Constants.R /\
      0 <= mid_stateOpening1AtZ < Constants.R /\
      0 <= mid_stateOpening2AtZ < Constants.R /\
      0 <= proofLookupGrandProductOpeningAtZOmega < Constants.R /\
      0 <= powerOfAlpha6 < Constants.R /\
      0 <= zMinusLastOmega < Constants.R /\
      0 <= v < Constants.R /\
      0 <= proofLookupTPolyOpeningAtZOmega < Constants.R /\
      0 <= betaLookup < Constants.R /\
      0 <= betaGammaPlusGamma < Constants.R /\
      0 <= eta_L < Constants.R /\
      0 <= proofLookupTableTypePolyOpeningAtZ < Constants.R /\
      0 <= proofLookupSelectorPolyOpeningAtZ < Constants.R /\
      0 <= gammaLookup < Constants.R /\
      0 <= betaPlusOne < Constants.R /\
      0 <= powerOfAlpha7 < Constants.R /\
      0 <= l0AtZ < Constants.R /\
      0 <= powerOfAlpha8 < Constants.R /\
      0 <= lNMinusOneAtZ < Constants.R /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = proofLookupGrandProductOpeningAtZOmega /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_6_SLOT) = powerOfAlpha6 /\
      W256.to_uint (load Primops.memory{1} STATE_Z_MINUS_LAST_OMEGA_SLOT) = zMinusLastOmega /\
      W256.to_uint (load Primops.memory{1} STATE_V_SLOT) = v /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) = proofLookupTPolyOpeningAtZOmega /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_LOOKUP_SLOT) = betaLookup /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) = proofLookupTPolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) = betaGammaPlusGamma /\
      W256.to_uint (load Primops.memory{1} STATE_ETA_SLOT) = eta_L /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) = proofLookupTableTypePolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) = proofLookupSelectorPolyOpeningAtZ /\
      W256.to_uint (load Primops.memory{1} STATE_GAMMA_LOOKUP_SLOT) = gammaLookup /\
      W256.to_uint (load Primops.memory{1} STATE_BETA_PLUS_ONE_SLOT) = betaPlusOne /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_7_SLOT) = powerOfAlpha7 /\
      W256.to_uint (load Primops.memory{1} STATE_L_0_AT_Z_SLOT) = l0AtZ /\
      W256.to_uint (load Primops.memory{1} STATE_POWER_OF_ALPHA_8_SLOT) = powerOfAlpha8 /\
      W256.to_uint (load Primops.memory{1} STATE_L_N_MINUS_ONE_AT_Z_SLOT) = lNMinusOneAtZ
      ==>
      W256.to_uint res{1}.`1 = res{2}.`1 /\
        W256.to_uint res{1}.`2 = res{2}.`2 ).
        by smt(). by progress. exact addAssignLookupLinearisationContributionWithV_low_no_reassignment_and_mstore_equiv_low'.
        exact addAssignLookupLinearisationContributionWithV_low_no_reassignment_and_mstore_equiv_mid.
qed.

lemma addAssignLookupLinearisationContributionWithV_mid_equiv_high:
equiv [
    AddAssignLookupLinearisationContributionWithV.mid ~ AddAssignLookupLinearisationContributionWithV.high:
      stateOpening0AtZ{1} = FieldR.asint stateOpening0AtZ{2} /\
    stateOpening1AtZ{1} = FieldR.asint stateOpening1AtZ{2} /\
    stateOpening2AtZ{1} = FieldR.asint stateOpening2AtZ{2} /\
    proofLookupGrandProductOpeningAtZOmega{1} = FieldR.asint proofLookupGrandProductOpeningAtZOmega{2} /\
    powerOfAlpha6{1} = FieldR.asint powerOfAlpha6{2} /\
    zMinusLastOmega{1} = FieldR.asint zMinusLastOmega{2} /\
    v{1} = FieldR.asint v{2} /\
    proofLookupTPolyOpeningAtZOmega{1} = FieldR.asint proofLookupTPolyOpeningAtZOmega{2} /\
    betaLookup{1} = FieldR.asint betaLookup{2} /\
    proofLookupTPolyOpeningAtZ{1} = FieldR.asint proofLookupTPolyOpeningAtZ{2} /\
    betaGammaPlusGamma{1} = FieldR.asint betaGammaPlusGamma{2} /\
    eta'{1} = FieldR.asint eta'{2} /\
    proofLookupTableTypePolyOpeningAtZ{1} = FieldR.asint proofLookupTableTypePolyOpeningAtZ{2} /\
    proofLookupSelectorPolyOpeningAtZ{1} = FieldR.asint proofLookupSelectorPolyOpeningAtZ{2} /\
    gammaLookup{1} = FieldR.asint gammaLookup{2} /\
    betaPlusOne{1} = FieldR.asint betaPlusOne{2} /\
    powerOfAlpha7{1} = FieldR.asint powerOfAlpha7{2} /\
    l0AtZ{1} = FieldR.asint l0AtZ{2} /\
    powerOfAlpha8{1} = FieldR.asint powerOfAlpha8{2} /\
      lNMinusOneAtZ{1} = FieldR.asint lNMinusOneAtZ{2} ==>
    res{1}.`1 = FieldR.asint res{2}.`1 /\
    res{1}.`2 = FieldR.asint res{2}.`2
    ].
    proof.
      proc.
      wp. skip. progress.
      do rewrite FieldR.mulE.
      rewrite Constants.r_eq_fieldr_p.
      rewrite (modzMml (FieldR.asint v{2} * _) _).
      rewrite modzMml. reflexivity.
      pose x1 := proofLookupTPolyOpeningAtZOmega{2} * betaLookup{2}.
      pose y1 := (FieldR.asint proofLookupTPolyOpeningAtZOmega{2}) * (FieldR.asint betaLookup{2}).
      pose x2 := x1 + proofLookupTPolyOpeningAtZ{2}.
      pose y2 := y1 + (FieldR.asint proofLookupTPolyOpeningAtZ{2}).
      pose x3 := x2 + betaGammaPlusGamma{2}.
      pose y3 := y2 + (FieldR.asint betaGammaPlusGamma{2}).
      pose x4 := eta'{2} * stateOpening1AtZ{2}.
      pose y4 := (FieldR.asint eta'{2}) * (FieldR.asint stateOpening1AtZ{2}).
      pose x5 := eta'{2} * eta'{2}.
      pose y5 := (FieldR.asint eta'{2}) * (FieldR.asint eta'{2}).
      pose x6 := x5 * stateOpening2AtZ{2}.
      pose y6 := y5 * (FieldR.asint stateOpening2AtZ{2}).
      pose x7 := x5 * eta'{2}.
      pose y7 := y5 * (FieldR.asint eta'{2}).
      pose x8 := x7 * proofLookupTableTypePolyOpeningAtZ{2}.
      pose y8 := y7 * (FieldR.asint proofLookupTableTypePolyOpeningAtZ{2}).
      pose x9 := stateOpening0AtZ{2} + x4.
      pose y9 := (FieldR.asint stateOpening0AtZ{2}) + y4.
      pose x10 := x9 + x6.
      pose y10 := y9 + y6.
      pose x11 := x10 + x8.
      pose y11 := y10 + y8.
      pose x12 := x11 * proofLookupSelectorPolyOpeningAtZ{2}.
      pose y12 := y11 * (FieldR.asint proofLookupSelectorPolyOpeningAtZ{2}).
      pose x13 := x12 + gammaLookup{2}.
      pose y13 := y12 + (FieldR.asint gammaLookup{2}).
      pose x14 := x3 * x13.
      pose y14 := y3 * y13.
      pose x15 := -x14.
      pose y15 := -y14.
      pose x16 := x15 * betaPlusOne{2}.
      pose y16 := y15 * (FieldR.asint betaPlusOne{2}).
      pose x17 := x16 * powerOfAlpha6{2}.
      pose y17 := y16 * (FieldR.asint powerOfAlpha6{2}).
      pose x18 := x17 * zMinusLastOmega{2}.
      pose y18 := y17 * (FieldR.asint zMinusLastOmega{2}).
      pose x19 := powerOfAlpha7{2} * l0AtZ{2}.
      pose y19 := (FieldR.asint powerOfAlpha7{2}) * (FieldR.asint l0AtZ{2}).
      pose x20 := powerOfAlpha8{2} * lNMinusOneAtZ{2}.
      pose y20 := (FieldR.asint powerOfAlpha8{2}) * (FieldR.asint lNMinusOneAtZ{2}).    
      pose x21 := x18 + x19.
      pose y21 := y18 + y19.
      pose x22 := x21 + x20.
      pose y22 := y21 + y20.    
      rewrite FieldR.mulE. rewrite -modzMml. congr. congr. congr.
      rewrite /x22 /y22. rewrite FieldR.addE. rewrite -modzDm. congr. congr. congr.
      rewrite /x21 /y21. rewrite FieldR.addE. rewrite -modzDm. congr. congr. congr.
      rewrite /x18 /y18. rewrite FieldR.mulE. rewrite -modzMml. congr. congr. congr.
      rewrite /x17 /y17. rewrite FieldR.mulE. rewrite -modzMml. congr. congr. congr.
      rewrite /x16 /y16. rewrite FieldR.mulE. rewrite -modzMml. congr. congr. congr.
      rewrite /x15 /y15. rewrite FieldR.oppE. rewrite -modzNm. congr. congr. congr.
      rewrite /x14 /y14. rewrite FieldR.mulE. rewrite -modzMm. congr. congr. congr.
      rewrite /x3 /y3. rewrite FieldR.addE. rewrite -modzDml. congr. congr. congr.
      rewrite /x2 /y2. rewrite FieldR.addE. rewrite -modzDml. congr. congr. congr.
      rewrite /x1 /y1. rewrite FieldR.mulE. rewrite Constants.r_eq_fieldr_p. reflexivity.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      rewrite /x13 /y13. rewrite FieldR.addE. rewrite -modzDml. congr. congr. congr.
      rewrite /x12 /y12. rewrite FieldR.mulE. rewrite -modzMml. congr. congr. congr.
      rewrite /x11 /y11. rewrite FieldR.addE. rewrite -modzDm. congr. congr. congr.
      rewrite /x10 /y10. rewrite FieldR.addE. rewrite -modzDm. congr. congr. congr.
      rewrite /x9 /y9. rewrite FieldR.addE. rewrite -modzDmr. congr. congr. congr.
      rewrite /x4 /y4. rewrite FieldR.mulE. rewrite Constants.r_eq_fieldr_p. reflexivity.
      exact Constants.r_eq_fieldr_p.
      rewrite /x6 /y6. rewrite FieldR.mulE. rewrite -modzMml. congr. congr. congr.
      rewrite /x5 /y5. rewrite FieldR.mulE. rewrite Constants.r_eq_fieldr_p. reflexivity.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      rewrite /x8 /y8. rewrite FieldR.mulE. rewrite -modzMml. congr. congr. congr.
      rewrite /x7 /y7. rewrite FieldR.mulE. rewrite -modzMml. congr. congr. congr.
      rewrite /x5 /y5. rewrite FieldR.mulE. rewrite Constants.r_eq_fieldr_p. reflexivity.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
      rewrite /x19 /y19. rewrite FieldR.mulE. rewrite Constants.r_eq_fieldr_p. reflexivity.
      exact Constants.r_eq_fieldr_p.
      rewrite /x20 /y20. rewrite FieldR.mulE. rewrite Constants.r_eq_fieldr_p. reflexivity.
      exact Constants.r_eq_fieldr_p.
      exact Constants.r_eq_fieldr_p.
  qed.


    
