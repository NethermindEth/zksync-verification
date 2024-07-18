pragma Goals:printall.

require        Constants.
require import PurePrimops.
require import RevertWithMessage.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module LoadProof = {
    proc low(): unit = {
  var offset, publicInputLengthInWords, isValid, _4, _7, _8, proofLengthInWords, tmp99, _15, x, _18, y, xx, _20, _21, _22, _23, _28, x_1, _31, y_1, xx_1, _32, _33, _34, _35, _40, x_2, _43, y_2, xx_2, _44, _45, _46, _47, _52, x_3, _55, y_3, xx_3, _56, _57, _58, _59, _64, x_4, _67, y_4, xx_4, _68, _69, _70, _71, _76, x_5, _79, y_5, xx_5, _80, _81, _82, _83, _88, x_6, _91, y_6, xx_6, _92, _93, _94, _95, _100, x_7, _103, y_7, xx_7, _104, _105, _106, _107, _112, x_8, _115, y_8, xx_8, _116, _117, _118, _119, _124, x_9, _127, y_9, xx_9, _128, _129, _130, _131, _136, x_10, _139, y_10, xx_10, _140, _141, _142, _143, _149, _154, _159, _164, _169, _174, _179, _184, _189, _194, _199, _204, _209, _214, _219, _224, _229, _234, _239, x_11, _242, y_11, xx_11, _243, _244, _245, _246, _251, x_12, _254, y_12, xx_12, _255, _256, _257, _258, recursiveProofLengthInWords, _263, _264, _265, _267, x_13, _269, y_13, xx_13, _270, _271, _272, _273, _276, _277, x_14, _279, y_14, xx_14, _280, _281, _282, _283;
    offset <@ Primops.calldataload(W256.of_int 4);
    publicInputLengthInWords <@ Primops.calldataload(offset + W256.of_int 4);
    isValid <- (PurePrimops.eq_uint256 publicInputLengthInWords W256.one);
    _4 <- ((PurePrimops.shl (W256.of_int 253) (W256.of_int 1)) - (W256.of_int 1));
    _7 <@ Primops.calldataload(offset + (W256.of_int 36));
    _8 <- (PurePrimops.bit_and _7 _4);
    Primops.mstore(PROOF_PUBLIC_INPUT, _8);
    offset <@ Primops.calldataload(W256.of_int 36);
    tmp99 <@ Primops.calldataload(offset + W256.of_int 4);
    proofLengthInWords <- tmp99;
    isValid <- (PurePrimops.bit_and (PurePrimops.eq_uint256 proofLengthInWords (W256.of_int 44)) isValid);
    _15 <@ Primops.calldataload(offset + W256.of_int 36);
    x <- (_15 %% Q_MOD);
    _18 <@ Primops.calldataload(offset + W256.of_int 68);
    y <- (_18 %% Q_MOD);
    xx <- (PurePrimops.mulmod x x Q_MOD);
    _20 <- (PurePrimops.mulmod x xx Q_MOD);
    _21 <- (PurePrimops.addmod _20 (W256.of_int 3) Q_MOD);
    _22 <- (PurePrimops.mulmod y y Q_MOD);
    _23 <- (PurePrimops.eq_uint256 _22 _21);
    isValid <- (PurePrimops.bit_and _23 isValid);
    Primops.mstore(PROOF_STATE_POLYS_0_X_SLOT, x);
    Primops.mstore(PROOF_STATE_POLYS_0_Y_SLOT, y);
    _28 <@ Primops.calldataload(offset + W256.of_int 100);
    x_1 <- (_28 %% Q_MOD);
    _31 <@ Primops.calldataload(offset + W256.of_int 132);
    y_1 <- (_31 %% Q_MOD);
    xx_1 <- (PurePrimops.mulmod x_1 x_1 Q_MOD);
    _32 <- (PurePrimops.mulmod x_1 xx_1 Q_MOD);
    _33 <- (PurePrimops.addmod _32 (W256.of_int 3) Q_MOD);
    _34 <- (PurePrimops.mulmod y_1 y_1 Q_MOD);
    _35 <- (PurePrimops.eq_uint256 _34 _33);
    isValid <- (PurePrimops.bit_and _35 isValid);
    Primops.mstore(PROOF_STATE_POLYS_1_X_SLOT, x_1);
    Primops.mstore(PROOF_STATE_POLYS_1_Y_SLOT, y_1);
    _40 <@ Primops.calldataload(offset + W256.of_int 164);
    x_2 <- (_40 %% Q_MOD);
    _43 <@ Primops.calldataload(offset + W256.of_int 196);
    y_2 <- (_43 %% Q_MOD);
    xx_2 <- (PurePrimops.mulmod x_2 x_2 Q_MOD);
    _44 <- (PurePrimops.mulmod x_2 xx_2 Q_MOD);
    _45 <- (PurePrimops.addmod _44 (W256.of_int 3) Q_MOD);
    _46 <- (PurePrimops.mulmod y_2 y_2 Q_MOD);
    _47 <- (PurePrimops.eq_uint256 _46 _45);
    isValid <- (PurePrimops.bit_and _47 isValid);
    Primops.mstore(PROOF_STATE_POLYS_2_X_SLOT, x_2);
    Primops.mstore(PROOF_STATE_POLYS_2_Y_SLOT, y_2);
    _52 <@ Primops.calldataload(offset + W256.of_int 228);
    x_3 <- (_52 %% Q_MOD);
    _55 <@ Primops.calldataload(offset + W256.of_int 260);
    y_3 <- (_55 %% Q_MOD);
    xx_3 <- (PurePrimops.mulmod x_3 x_3 Q_MOD);
    _56 <- (PurePrimops.mulmod x_3 xx_3 Q_MOD);
    _57 <- (PurePrimops.addmod _56 (W256.of_int 3) Q_MOD);
    _58 <- (PurePrimops.mulmod y_3 y_3 Q_MOD);
    _59 <- (PurePrimops.eq_uint256 _58 _57);
    isValid <- (PurePrimops.bit_and _59 isValid);
    Primops.mstore(PROOF_STATE_POLYS_3_X_SLOT, x_3);
    Primops.mstore(PROOF_STATE_POLYS_3_Y_SLOT, y_3);
    _64 <@ Primops.calldataload(offset + W256.of_int 292);
    x_4 <- (_64 %% Q_MOD);
    _67 <@ Primops.calldataload(offset + W256.of_int 324);
    y_4 <- (_67 %% Q_MOD);
    xx_4 <- (PurePrimops.mulmod x_4 x_4 Q_MOD);
    _68 <- (PurePrimops.mulmod x_4 xx_4 Q_MOD);
    _69 <- (PurePrimops.addmod _68 (W256.of_int 3) Q_MOD);
    _70 <- (PurePrimops.mulmod y_4 y_4 Q_MOD);
    _71 <- (PurePrimops.eq_uint256 _70 _69);
    isValid <- (PurePrimops.bit_and _71 isValid);
    Primops.mstore(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT, x_4);
    Primops.mstore(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT, y_4);
    _76 <@ Primops.calldataload(offset + W256.of_int 356);
    x_5 <- (_76 %% Q_MOD);
    _79 <@ Primops.calldataload(offset + W256.of_int 388);
    y_5 <- (_79 %% Q_MOD);
    xx_5 <- (PurePrimops.mulmod x_5 x_5 Q_MOD);
    _80 <- (PurePrimops.mulmod x_5 xx_5 Q_MOD);
    _81 <- (PurePrimops.addmod _80 (W256.of_int 3) Q_MOD);
    _82 <- (PurePrimops.mulmod y_5 y_5 Q_MOD);
    _83 <- (PurePrimops.eq_uint256 _82 _81);
    isValid <- (PurePrimops.bit_and _83 isValid);
    Primops.mstore(PROOF_LOOKUP_S_POLY_X_SLOT, x_5);
    Primops.mstore(PROOF_LOOKUP_S_POLY_Y_SLOT, y_5);
    _88 <@ Primops.calldataload(offset + W256.of_int 420);
    x_6 <- (_88 %% Q_MOD);
    _91 <@ Primops.calldataload(offset + W256.of_int 452);
    y_6 <- (_91 %% Q_MOD);
    xx_6 <- (PurePrimops.mulmod x_6 x_6 Q_MOD);
    _92 <- (PurePrimops.mulmod x_6 xx_6 Q_MOD);
    _93 <- (PurePrimops.addmod _92 (W256.of_int 3) Q_MOD);
    _94 <- (PurePrimops.mulmod y_6 y_6 Q_MOD);
    _95 <- (PurePrimops.eq_uint256 _94 _93);
    isValid <- (PurePrimops.bit_and _95 isValid);
    Primops.mstore(PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT, x_6);
    Primops.mstore(PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT, y_6);
    _100 <@ Primops.calldataload(offset + W256.of_int 484);
    x_7 <- (_100 %% Q_MOD);
    _103 <@ Primops.calldataload(offset + W256.of_int 516);
    y_7 <- (_103 %% Q_MOD);
    xx_7 <- (PurePrimops.mulmod x_7 x_7 Q_MOD);
    _104 <- (PurePrimops.mulmod x_7 xx_7 Q_MOD);
    _105 <- (PurePrimops.addmod _104 (W256.of_int 3) Q_MOD);
    _106 <- (PurePrimops.mulmod y_7 y_7 Q_MOD);
    _107 <- (PurePrimops.eq_uint256 _106 _105);
    isValid <- (PurePrimops.bit_and _107 isValid);
    Primops.mstore(PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT, x_7);
    Primops.mstore(PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT, y_7);
    _112 <@ Primops.calldataload(offset + W256.of_int 548);
    x_8 <- (_112 %% Q_MOD);
    _115 <@ Primops.calldataload(offset + W256.of_int 580);
    y_8 <- (_115 %% Q_MOD);
    xx_8 <- (PurePrimops.mulmod x_8 x_8 Q_MOD);
    _116 <- (PurePrimops.mulmod x_8 xx_8 Q_MOD);
    _117 <- (PurePrimops.addmod _116 (W256.of_int 3) Q_MOD);
    _118 <- (PurePrimops.mulmod y_8 y_8 Q_MOD);
    _119 <- (PurePrimops.eq_uint256 _118 _117);
    isValid <- (PurePrimops.bit_and _119 isValid);
    Primops.mstore(PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT, x_8);
    Primops.mstore(PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT, y_8);
    _124 <@ Primops.calldataload(offset + W256.of_int 612);
    x_9 <- (_124 %% Q_MOD);
    _127 <@ Primops.calldataload(offset + W256.of_int 644);
    y_9 <- (_127 %% Q_MOD);
    xx_9 <- (PurePrimops.mulmod x_9 x_9 Q_MOD);
    _128 <- (PurePrimops.mulmod x_9 xx_9 Q_MOD);
    _129 <- (PurePrimops.addmod _128 (W256.of_int 3) Q_MOD);
    _130 <- (PurePrimops.mulmod y_9 y_9 Q_MOD);
    _131 <- (PurePrimops.eq_uint256 _130 _129);
    isValid <- (PurePrimops.bit_and _131 isValid);
    Primops.mstore(PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT, x_9);
    Primops.mstore(PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT, y_9);
    _136 <@ Primops.calldataload(offset + W256.of_int 676);
    x_10 <- (_136 %% Q_MOD);
    _139 <@ Primops.calldataload(offset + W256.of_int 708);
    y_10 <- (_139 %% Q_MOD);
    xx_10 <- (PurePrimops.mulmod x_10 x_10 Q_MOD);
    _140 <- (PurePrimops.mulmod x_10 xx_10 Q_MOD);
    _141 <- (PurePrimops.addmod _140 (W256.of_int 3) Q_MOD);
    _142 <- (PurePrimops.mulmod y_10 y_10 Q_MOD);
    _143 <- (PurePrimops.eq_uint256 _142 _141);
    isValid <- (PurePrimops.bit_and _143 isValid);
    Primops.mstore(PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT, x_10);
    Primops.mstore(PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT, y_10);
    _149 <@ Primops.calldataload(offset + W256.of_int 740);
    Primops.mstore(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT, _149 %% R_MOD);
    _154 <@ Primops.calldataload(offset + W256.of_int 772);
    Primops.mstore(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT, _154 %% R_MOD);
    _159 <@ Primops.calldataload(offset + W256.of_int 804);
    Primops.mstore(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT, _159 %% R_MOD);
    _164 <@ Primops.calldataload(offset + W256.of_int 836);
    Primops.mstore(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT, _164 %% R_MOD);
    _169 <@ Primops.calldataload(offset + W256.of_int 868);
    Primops.mstore(PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT, _169 %% R_MOD);
    _174 <@ Primops.calldataload(offset + W256.of_int 900);
    Primops.mstore(PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT, _174 %% R_MOD);
    _179 <@ Primops.calldataload(offset + W256.of_int 932);
    Primops.mstore(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT, _179 %% R_MOD);
    _184 <@ Primops.calldataload(offset + W256.of_int 964);
    Primops.mstore(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT, _184 %% R_MOD);
    _189 <@ Primops.calldataload(offset + W256.of_int 996);
    Primops.mstore(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT, _189 %% R_MOD);
    _194 <@ Primops.calldataload(offset + W256.of_int 1028);
    Primops.mstore(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT, _194 %% R_MOD);
    _199 <@ Primops.calldataload(offset + W256.of_int 1060);
    Primops.mstore(PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT, _199 %% R_MOD);
    _204 <@ Primops.calldataload(offset + W256.of_int 1092);
    Primops.mstore(PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT, _204 %% R_MOD);
    _209 <@ Primops.calldataload(offset + W256.of_int 1124);
    Primops.mstore(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT, _209 %% R_MOD);
    _214 <@ Primops.calldataload(offset + W256.of_int 1156);
    Primops.mstore(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT, _214 %% R_MOD);
    _219 <@ Primops.calldataload(offset + W256.of_int 1188);
    Primops.mstore(PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT, _219 %% R_MOD);
    _224 <@ Primops.calldataload(offset + W256.of_int 1220);
    Primops.mstore(PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT, _224 %% R_MOD);
    _229 <@ Primops.calldataload(offset + W256.of_int 1252);
    Primops.mstore(PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT, _229 %% R_MOD);
    _234 <@ Primops.calldataload(offset + W256.of_int 1284);
    Primops.mstore(PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT, _234 %% R_MOD);
    _239 <@ Primops.calldataload(offset + W256.of_int 1316);
    x_11 <- (_239 %% Q_MOD);
    _242 <@ Primops.calldataload(offset + W256.of_int 1348);
    y_11 <- (_242 %% Q_MOD);
    xx_11 <- (PurePrimops.mulmod x_11 x_11 Q_MOD);
    _243 <- (PurePrimops.mulmod x_11 xx_11 Q_MOD);
    _244 <- (PurePrimops.addmod _243 (W256.of_int 3) Q_MOD);
    _245 <- (PurePrimops.mulmod y_11 y_11 Q_MOD);
    _246 <- (PurePrimops.eq_uint256 _245 _244);
    isValid <- (PurePrimops.bit_and _246 isValid);
    Primops.mstore(PROOF_OPENING_PROOF_AT_Z_X_SLOT, x_11);
    Primops.mstore(PROOF_OPENING_PROOF_AT_Z_Y_SLOT, y_11);
    _251 <@ Primops.calldataload(offset + W256.of_int 1380);
    x_12 <- (_251 %% Q_MOD);
    _254 <@ Primops.calldataload(offset + W256.of_int 1412);
    y_12 <- (_254 %% Q_MOD);
    xx_12 <- (PurePrimops.mulmod x_12 x_12 Q_MOD);
    _255 <- (PurePrimops.mulmod x_12 xx_12 Q_MOD);
    _256 <- (PurePrimops.addmod _255 (W256.of_int 3) Q_MOD);
    _257 <- (PurePrimops.mulmod y_12 y_12 Q_MOD);
    _258 <- (PurePrimops.eq_uint256 _257 _256);
    isValid <- (PurePrimops.bit_and _258 isValid);
    Primops.mstore(PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT, x_12);
    Primops.mstore(PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT, y_12);
    offset <@ Primops.calldataload(W256.of_int 68);
    recursiveProofLengthInWords <@ Primops.calldataload(offset + W256.of_int 4);
    _263 <@ Primops.mload(VK_RECURSIVE_FLAG_SLOT);
    if ((_263 = W256.zero))
    {
      _264 <- (PurePrimops.iszero recursiveProofLengthInWords);
      isValid <- (PurePrimops.bit_and _264 isValid);
    } else {
      _265 <- (PurePrimops.eq_uint256 recursiveProofLengthInWords (W256.of_int 4));
      isValid <- (PurePrimops.bit_and _265 isValid);
      _267 <@ Primops.calldataload(offset + W256.of_int 36);
      x_13 <- (_267 %% Q_MOD);
      _269 <@ Primops.calldataload(offset + W256.of_int 68);
      y_13 <- (_269 %% Q_MOD);
      xx_13 <- (PurePrimops.mulmod x_13 x_13 Q_MOD);
      _270 <- (PurePrimops.mulmod x_13 xx_13 Q_MOD);
      _271 <- (PurePrimops.addmod _270 (W256.of_int 3) Q_MOD);
      _272 <- (PurePrimops.mulmod y_13 y_13 Q_MOD);
      _273 <- (PurePrimops.eq_uint256 _272 _271);
      isValid <- (PurePrimops.bit_and _273 isValid);
      Primops.mstore(PROOF_RECURSIVE_PART_P1_X_SLOT, x_13);
      Primops.mstore(PROOF_RECURSIVE_PART_P1_Y_SLOT, y_13);
      _276 <- (offset + W256.of_int 100);
      _277 <@ Primops.calldataload(_276);
      x_14 <- (_277 %% Q_MOD);
      _279 <@ Primops.calldataload((offset + W256.of_int 132));
      y_14 <- (_279 %% Q_MOD);
      xx_14 <- (PurePrimops.mulmod x_14 x_14 Q_MOD);
      _280 <- (PurePrimops.mulmod x_14 xx_14 Q_MOD);
      _281 <- (PurePrimops.addmod _280 (W256.of_int 3) Q_MOD);
      _282 <- (PurePrimops.mulmod y_14 y_14 Q_MOD);
      _283 <- (PurePrimops.eq_uint256 _282 _281);
      isValid <- (PurePrimops.bit_and _283 isValid);
      Primops.mstore(PROOF_RECURSIVE_PART_P2_X_SLOT, x_14);
      Primops.mstore(PROOF_RECURSIVE_PART_P2_Y_SLOT, y_14);
    }
    
    if ((bool_of_uint256 (PurePrimops.iszero isValid)))
    {
      RevertWithMessage.low(W256.of_int 27, W256.of_int STRING (*loadProof: Proof is invalid*));
    }
  }
}.

lemma loadProof_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_loadProof ~ LoadProof.low:
      ={arg, glob LoadProof} ==>
      ={res, glob LoadProof}
    ].
    proof.
      proc.
      seq 16 7: (#pre /\ _1{1} = W256.of_int 4 /\ _5{1} = W256.of_int 36 /\ usr_isValid{1} = isValid{2}). inline*. wp. skip. by progress.
      seq 29 16: (#pre /\ usr_y{1} = y{2} /\ _13{1} = Q_MOD /\ _16{1} = W256.of_int 68 /\ _19{1} = W256.of_int 3 /\ usr_offset{1} = offset{2}). inline*. wp. skip. rewrite /Constants.Q. by progress.
      seq 20 12: (#pre /\ _26{1} = W256.of_int 100 /\ _29{1} = W256.of_int 132). inline*. wp. skip. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      seq 127 36: #pre. inline*. wp. skip. rewrite /Constants.R. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      seq 20 12: #pre. inline*. wp. skip. by progress.
      sp.
      seq 5 2 : (#pre /\ usr_recursiveProofLengthInWords{1} = recursiveProofLengthInWords{2}). inline*. wp. skip. by progress.
      seq 3 1 : (#pre /\ ={_263}). inline*. wp. skip. by progress.
      sp. if. by progress.
      sp. if. by progress.
      sp. call revertWithMessage_extracted_equiv_low. skip. by progress.
      skip. by progress.
      seq 20 14: #pre. inline*. wp. skip. by progress.
      seq 18 13: #pre. inline*. wp. skip. by progress.
      sp. if. by progress.
      sp. call revertWithMessage_extracted_equiv_low. skip. by progress.
      skip. by progress.
    qed.
    
