require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

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
    
      
