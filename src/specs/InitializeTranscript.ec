require        Constants.
require import GetTranscriptChallenge.
require import Modexp.
require import PurePrimops.
require import UInt256.
require import UpdateTranscript.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module InitializeTranscript = {
  proc low(): unit = {
    var _2, _4, _6, _8, _10, _12, _14, _16, _18, _20, _23, _25, _27, _30, _33, _35, _37, _40, _43, _45, _47, _50, _52, _54, _56, _58, _60, _62, _64, z, _68, _71, _73, _75, _77, _79, _81, _83, _85, _87, _89, _91, _93, _95, _97, _99, _101, _103, _105, _107, _110, _112, _114, _116, _118;
    _2 <@ Primops.mload(PROOF_PUBLIC_INPUT);
    UpdateTranscript.low(_2);
    _4 <@ Primops.mload(PROOF_STATE_POLYS_0_X_SLOT);
    UpdateTranscript.low(_4);
    _6 <@ Primops.mload(PROOF_STATE_POLYS_0_Y_SLOT);
    UpdateTranscript.low(_6);
    _8 <@ Primops.mload(PROOF_STATE_POLYS_1_X_SLOT);
    UpdateTranscript.low(_8);
    _10 <@ Primops.mload(PROOF_STATE_POLYS_1_Y_SLOT);
    UpdateTranscript.low(_10);
    _12 <@ Primops.mload(PROOF_STATE_POLYS_2_X_SLOT);
    UpdateTranscript.low(_12);
    _14 <@ Primops.mload(PROOF_STATE_POLYS_2_Y_SLOT);
    UpdateTranscript.low(_14);
    _16 <@ Primops.mload(PROOF_STATE_POLYS_3_X_SLOT);
    UpdateTranscript.low(_16);
    _18 <@ Primops.mload(PROOF_STATE_POLYS_3_Y_SLOT);
    UpdateTranscript.low(_18);
    _20 <@ GetTranscriptChallenge.low(W256.zero);
    Primops.mstore(STATE_ETA_SLOT, _20);
    _23 <@ Primops.mload(PROOF_LOOKUP_S_POLY_X_SLOT);
    UpdateTranscript.low(_23);
    _25 <@ Primops.mload(PROOF_LOOKUP_S_POLY_Y_SLOT);
    UpdateTranscript.low(_25);
    _27 <@ GetTranscriptChallenge.low(W256.one);
    Primops.mstore(STATE_BETA_SLOT, _27);
    _30 <@ GetTranscriptChallenge.low(W256.of_int 2);
    Primops.mstore(STATE_GAMMA_SLOT, _30);
    _33 <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT);
    UpdateTranscript.low(_33);
    _35 <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT);
    UpdateTranscript.low(_35);
    _37 <@ GetTranscriptChallenge.low(W256.of_int 3);
    Primops.mstore(STATE_BETA_LOOKUP_SLOT, _37);
    _40 <@ GetTranscriptChallenge.low(W256.of_int 4);
    Primops.mstore(STATE_GAMMA_LOOKUP_SLOT, _40);
    _43 <@ Primops.mload(PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT);
    UpdateTranscript.low(_43);
    _45 <@ Primops.mload(PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT);
    UpdateTranscript.low(_45);
    _47 <@ GetTranscriptChallenge.low(W256.of_int 5);
    Primops.mstore(STATE_ALPHA_SLOT, _47);
    _50 <@ Primops.mload(PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT);
    UpdateTranscript.low(_50);
    _52 <@ Primops.mload(PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT);
    UpdateTranscript.low(_52);
    _54 <@ Primops.mload(PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT);
    UpdateTranscript.low(_54);
    _56 <@ Primops.mload(PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT);
    UpdateTranscript.low(_56);
    _58 <@ Primops.mload(PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT);
    UpdateTranscript.low(_58);
    _60 <@ Primops.mload(PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT);
    UpdateTranscript.low(_60);
    _62 <@ Primops.mload(PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT);
    UpdateTranscript.low(_62);
    _64 <@ Primops.mload(PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT);
    UpdateTranscript.low(_64);
    z <@ GetTranscriptChallenge.low(W256.of_int 6);
    Primops.mstore(STATE_Z_SLOT, z);
    _68 <@ Modexp.low(z, DOMAIN_SIZE);
    Primops.mstore(STATE_Z_IN_DOMAIN_SIZE, _68);
    _71 <@ Primops.mload(PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_71);
    _73 <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_73);
    _75 <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_75);
    _77 <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_77);
    _79 <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_79);
    _81 <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT);
    UpdateTranscript.low(_81);
    _83 <@ Primops.mload(PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_83);
    _85 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_85);
    _87 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_87);
    _89 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_89);
    _91 <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    UpdateTranscript.low(_91);
    _93 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_93);
    _95 <@ Primops.mload(PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_95);
    _97 <@ Primops.mload(PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_97);
    _99 <@ Primops.mload(PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT);
    UpdateTranscript.low(_99);
    _101 <@ Primops.mload(PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    UpdateTranscript.low(_101);
    _103 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT);
    UpdateTranscript.low(_103);
    _105 <@ Primops.mload(PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT);
    UpdateTranscript.low(_105);
    _107 <@ GetTranscriptChallenge.low(W256.of_int 7);
    Primops.mstore(STATE_V_SLOT, _107);
    _110 <@ Primops.mload(PROOF_OPENING_PROOF_AT_Z_X_SLOT);
    UpdateTranscript.low(_110);
    _112 <@ Primops.mload(PROOF_OPENING_PROOF_AT_Z_Y_SLOT);
    UpdateTranscript.low(_112);
    _114 <@ Primops.mload(PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT);
    UpdateTranscript.low(_114);
    _116 <@ Primops.mload(PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT);
    UpdateTranscript.low(_116);
    _118 <@ GetTranscriptChallenge.low(W256.of_int 8);
    Primops.mstore(STATE_U_SLOT, _118);
    }
}.

lemma initializeTranscript_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_initializeTranscript ~ InitializeTranscript.low :
      ={arg, glob InitializeTranscript} ==>
      ={res, glob InitializeTranscript}
    ].
proof.
  proc.
  inline Primops.mload Primops.mstore.
  do 9! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  seq 7 4: #pre. wp. call getTranscriptChallenge_extracted_equiv_low. wp. skip. by progress.
  do 2! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  do 2! (seq 7 4: #pre; first wp; first call getTranscriptChallenge_extracted_equiv_low; first wp; first skip; first by progress).
  do 2! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  do 2! (seq 7 4: #pre; first wp; first call getTranscriptChallenge_extracted_equiv_low; first wp; first skip; first by progress).
  do 2! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  do 1! (seq 7 4: #pre; first wp; first call getTranscriptChallenge_extracted_equiv_low; first wp; first skip; first by progress).
  do 8! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  seq 14 8: #pre. wp. call modexp_extracted_equiv_low. wp. call getTranscriptChallenge_extracted_equiv_low. wp. skip. by progress.
  do 18! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  do 1! (seq 7 4: #pre; first wp; first call getTranscriptChallenge_extracted_equiv_low; first wp; first skip; first by progress).
  do 4! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  wp. call getTranscriptChallenge_extracted_equiv_low. wp. skip. by progress.
qed.
