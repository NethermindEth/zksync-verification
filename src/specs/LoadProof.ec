pragma Goals:printall.

require import AllCore.
require        Constants.
require import Field.
require import EllipticCurve.
require import PurePrimops.
require import RevertWithMessage.
require import Utils.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

op loadProof_memory_footprint (mem_0: mem)
  (recursive: bool)
  (proof_public_input: uint256)
  (state_poly_0 state_poly_1 state_poly_2 state_poly_3: uint256*uint256)
  (copy_permutation_grand_product: uint256*uint256)
  (lookup_s_poly lookup_grand_product: uint256*uint256)
  (quotient_poly_part_0 quotient_poly_part_1 quotient_poly_part_2 quotient_poly_part_3: uint256*uint256)
  (state_poly_0_opening_at_z state_poly_1_opening_at_z state_poly_2_opening_at_z state_poly_3_opening_at_z state_poly_3_opening_at_z_omega: uint256)
  (gate_selector_0_opening_at_z: uint256)
  (copy_permutation_poly_0_opening_at_z copy_permutation_poly_1_opening_at_z copy_permutation_poly_2_opening_at_z copy_permutation_grand_product_opening_at_z_omega: uint256)
  (lookup_s_poly_opening_at_z_omega lookup_grand_product_opening_at_z_omega lookup_t_poly_opening_at_z lookup_t_poly_opening_at_z_omega lookup_selector_poly_opening_at_z lookup_table_type_poly_opening_at_z: uint256)
  (quotient_poly_opening_at_z: uint256)
  (linearisation_poly_opening_at_z: uint256)
  (opening_proof_at_z opening_proof_at_z_omega: uint256*uint256)
  (recursive_part_p1 recursive_part_p2: uint256*uint256)
  =
  let mem_1 = store mem_0 PROOF_PUBLIC_INPUT proof_public_input in
  let mem_2 = store mem_1 PROOF_STATE_POLYS_0_X_SLOT state_poly_0.`1 in
  let mem_3 = store mem_2 PROOF_STATE_POLYS_0_Y_SLOT state_poly_0.`2 in
  let mem_4 = store mem_3 PROOF_STATE_POLYS_1_X_SLOT state_poly_1.`1 in
  let mem_5 = store mem_4 PROOF_STATE_POLYS_1_Y_SLOT state_poly_1.`2 in
  let mem_6 = store mem_5 PROOF_STATE_POLYS_2_X_SLOT state_poly_2.`1 in
  let mem_7 = store mem_6 PROOF_STATE_POLYS_2_Y_SLOT state_poly_2.`2 in
  let mem_8 = store mem_7 PROOF_STATE_POLYS_3_X_SLOT state_poly_3.`1 in
  let mem_9 = store mem_8 PROOF_STATE_POLYS_3_Y_SLOT state_poly_3.`2 in
  let mem_10 = store mem_9 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT copy_permutation_grand_product.`1 in
  let mem_11 = store mem_10 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT copy_permutation_grand_product.`2 in
  let mem_12 = store mem_11 PROOF_LOOKUP_S_POLY_X_SLOT lookup_s_poly.`1 in
  let mem_13 = store mem_12 PROOF_LOOKUP_S_POLY_Y_SLOT lookup_s_poly.`2 in
  let mem_14 = store mem_13 PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT lookup_grand_product.`1 in
  let mem_15 = store mem_14 PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT lookup_grand_product.`2 in
  let mem_16 = store mem_15 PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT quotient_poly_part_0.`1 in
  let mem_17 = store mem_16 PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT quotient_poly_part_0.`2 in
  let mem_18 = store mem_17 PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT quotient_poly_part_1.`1 in
  let mem_19 = store mem_18 PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT quotient_poly_part_1.`2 in
  let mem_20 = store mem_19 PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT quotient_poly_part_2.`1 in
  let mem_21 = store mem_20 PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT quotient_poly_part_2.`2 in
  let mem_22 = store mem_21 PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT quotient_poly_part_3.`1 in
  let mem_23 = store mem_22 PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT quotient_poly_part_3.`2 in
  let mem_24 = store mem_23 PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT state_poly_0_opening_at_z in
  let mem_25 = store mem_24 PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT state_poly_1_opening_at_z in
  let mem_26 = store mem_25 PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT state_poly_2_opening_at_z in
  let mem_27 = store mem_26 PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT state_poly_3_opening_at_z in
  let mem_28 = store mem_27 PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT state_poly_3_opening_at_z_omega in
  let mem_29 = store mem_28 PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT gate_selector_0_opening_at_z in
  let mem_30 = store mem_29 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT copy_permutation_poly_0_opening_at_z in
  let mem_31 = store mem_30 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT copy_permutation_poly_1_opening_at_z in
  let mem_32 = store mem_31 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT copy_permutation_poly_2_opening_at_z in
  let mem_33 = store mem_32 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT copy_permutation_grand_product_opening_at_z_omega in
  let mem_34 = store mem_33 PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT lookup_s_poly_opening_at_z_omega in
  let mem_35 = store mem_34 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT lookup_grand_product_opening_at_z_omega in
  let mem_36 = store mem_35 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT lookup_t_poly_opening_at_z in
  let mem_37 = store mem_36 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT lookup_t_poly_opening_at_z_omega in
  let mem_38 = store mem_37 PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT lookup_selector_poly_opening_at_z in
  let mem_39 = store mem_38 PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT lookup_table_type_poly_opening_at_z in
  let mem_40 = store mem_39 PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT quotient_poly_opening_at_z in
  let mem_41 = store mem_40 PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT linearisation_poly_opening_at_z in
  let mem_42 = store mem_41 PROOF_OPENING_PROOF_AT_Z_X_SLOT opening_proof_at_z.`1 in
  let mem_43 = store mem_42 PROOF_OPENING_PROOF_AT_Z_Y_SLOT opening_proof_at_z.`2 in
  let mem_44 = store mem_43 PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT opening_proof_at_z_omega.`1 in
  let mem_45 = store mem_44 PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT opening_proof_at_z_omega.`2 in
  if recursive
  then
    let mem_46 = store mem_45 PROOF_RECURSIVE_PART_P1_X_SLOT recursive_part_p1.`1 in
    let mem_47 = store mem_46 PROOF_RECURSIVE_PART_P1_Y_SLOT recursive_part_p1.`2 in
    let mem_48 = store mem_47 PROOF_RECURSIVE_PART_P2_X_SLOT recursive_part_p2.`1 in
    store mem_48 PROOF_RECURSIVE_PART_P2_Y_SLOT recursive_part_p2.`2
  else mem_45.

op on_curve_int (p: int*int) = 
  ((p.`1 * ((p.`1 * p.`1) %% Constants.Q) %% Constants.Q) + 3) %% Constants.Q =
  (p.`2 * p.`2) %% Constants.Q.

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

      proc mid(public_input_length_in_words: int, public_input: int, proof_length_in_words: int, state_poly_0: int*int, state_poly_1: int*int, state_poly_2: int*int, state_poly_3: int*int, copy_permutation_grand_product: int*int, lookup_s_poly: int*int, lookup_grand_product: int*int, quotient_poly_part_0: int*int, quotient_poly_part_1: int*int, quotient_poly_part_2: int*int, quotient_poly_part_3: int*int, state_poly_0_opening_at_z: int, state_poly_1_opening_at_z: int, state_poly_2_opening_at_z: int, state_poly_3_opening_at_z: int, state_poly_3_opening_at_z_omega: int, gate_selector_0_opening_at_z: int, copy_permutation_poly_0_opening_at_z: int, copy_permutation_poly_1_opening_at_z: int, copy_permutation_poly_2_opening_at_z: int, copy_permutation_grand_product_opening_at_z_omega: int, lookup_s_poly_opening_at_z_omega: int, lookup_grand_product_opening_at_z_omega: int, lookup_t_poly_opening_at_z: int, lookup_t_poly_opening_at_z_omega: int, lookup_selector_poly_opening_at_z: int, lookup_table_type_poly_opening_at_z: int, quotient_poly_opening_at_z: int, linearisation_poly_opening_at_z: int, opening_proof_at_z: int*int, opening_proof_at_z_omega: int*int, recursive_proof_length_in_words: int, vk_recursive_flag: bool, recursive_part_p1: int*int, recursive_part_p2: int*int): (int * (int * int) * (int * int) * (int * int) * (int * int) * (int *
    int) * (int * int) * (int * int) * (int * int) * (int * int) * (int *
    int) * (int * int) * int * int * int * int * int * int * int * int *
    int * int * int * int * int * int * int * int * int * int * (int * int) *
    (int * int) * (int * int) option * (int * int) option) option = {
  var ret_recursive_part_p1, ret_recursive_part_p2: (int*int) option;
  var isValid: bool;
  var ret;
    isValid <- public_input_length_in_words = 1;
    isValid <- isValid /\ (proof_length_in_words = 44);
    isValid <- isValid /\ on_curve_int state_poly_0;
    isValid <- isValid /\ on_curve_int state_poly_1;
    isValid <- isValid /\ on_curve_int state_poly_2;
    isValid <- isValid /\ on_curve_int state_poly_3;
    isValid <- isValid /\ on_curve_int copy_permutation_grand_product;
    isValid <- isValid /\ on_curve_int lookup_s_poly;
    isValid <- isValid /\ on_curve_int lookup_grand_product;
    isValid <- isValid /\ on_curve_int quotient_poly_part_0;
    isValid <- isValid /\ on_curve_int quotient_poly_part_1;
    isValid <- isValid /\ on_curve_int quotient_poly_part_2;
    isValid <- isValid /\ on_curve_int quotient_poly_part_3;
    isValid <- isValid /\ on_curve_int opening_proof_at_z;
    isValid <- isValid /\ on_curve_int opening_proof_at_z_omega;
    if (vk_recursive_flag) {
      isValid <- isValid /\ (recursive_proof_length_in_words = 4);
      isValid <- isValid /\ on_curve_int recursive_part_p1;
      ret_recursive_part_p1 <- Some (recursive_part_p1.`1 %% Constants.Q, recursive_part_p1.`2 %% Constants.Q);
      isValid <- isValid /\ on_curve_int recursive_part_p2;
      ret_recursive_part_p2 <- Some (recursive_part_p2.`1 %% Constants.Q, recursive_part_p2.`2 %% Constants.Q);
    } else {
      isValid <- isValid /\ (recursive_proof_length_in_words = 0);
      ret_recursive_part_p1 <- None;
      ret_recursive_part_p2 <- None;
    }

    if (isValid) {
      ret <- Some (
        public_input %% 2^253,
        (state_poly_0.`1 %% Constants.Q, state_poly_0.`2 %% Constants.Q),
        (state_poly_1.`1 %% Constants.Q, state_poly_1.`2 %% Constants.Q),
        (state_poly_2.`1 %% Constants.Q, state_poly_2.`2 %% Constants.Q),
        (state_poly_3.`1 %% Constants.Q, state_poly_3.`2 %% Constants.Q),
        (copy_permutation_grand_product.`1 %% Constants.Q, copy_permutation_grand_product.`2 %% Constants.Q),
        (lookup_s_poly.`1 %% Constants.Q, lookup_s_poly.`2 %% Constants.Q),
        (lookup_grand_product.`1 %% Constants.Q, lookup_grand_product.`2 %% Constants.Q),
        (quotient_poly_part_0.`1 %% Constants.Q, quotient_poly_part_0.`2 %% Constants.Q),
        (quotient_poly_part_1.`1 %% Constants.Q, quotient_poly_part_1.`2 %% Constants.Q),
        (quotient_poly_part_2.`1 %% Constants.Q, quotient_poly_part_2.`2 %% Constants.Q),
        (quotient_poly_part_3.`1 %% Constants.Q, quotient_poly_part_3.`2 %% Constants.Q),
        state_poly_0_opening_at_z %% Constants.R,
        state_poly_1_opening_at_z %% Constants.R,
        state_poly_2_opening_at_z %% Constants.R,
        state_poly_3_opening_at_z %% Constants.R,
        state_poly_3_opening_at_z_omega %% Constants.R,
        gate_selector_0_opening_at_z %% Constants.R,
        copy_permutation_poly_0_opening_at_z %% Constants.R,
        copy_permutation_poly_1_opening_at_z %% Constants.R,
        copy_permutation_poly_2_opening_at_z %% Constants.R,
        copy_permutation_grand_product_opening_at_z_omega %% Constants.R,
        lookup_s_poly_opening_at_z_omega %% Constants.R,
        lookup_grand_product_opening_at_z_omega %% Constants.R,
        lookup_t_poly_opening_at_z %% Constants.R,
        lookup_t_poly_opening_at_z_omega %% Constants.R,
        lookup_selector_poly_opening_at_z %% Constants.R,
        lookup_table_type_poly_opening_at_z %% Constants.R,
        quotient_poly_opening_at_z %% Constants.R,
        linearisation_poly_opening_at_z %% Constants.R,
        (opening_proof_at_z.`1 %% Constants.Q, opening_proof_at_z.`2 %% Constants.Q),
        (opening_proof_at_z_omega.`1 %% Constants.Q, opening_proof_at_z_omega.`2 %% Constants.Q),
        ret_recursive_part_p1,
        ret_recursive_part_p2
      );
    } else {
      ret <- None;
    }

    return ret;
    
    }

    proc high(public_input_length_in_words: int, public_input: FieldR.F, proof_length_in_words: int, state_poly_0: g, state_poly_1: g, state_poly_2: g, state_poly_3: g, copy_permutation_grand_product: g, lookup_s_poly: g, lookup_grand_product: g, quotient_poly_part_0: g, quotient_poly_part_1: g, quotient_poly_part_2: g, quotient_poly_part_3: g, state_poly_0_opening_at_z: FieldR.F, state_poly_1_opening_at_z: FieldR.F, state_poly_2_opening_at_z: FieldR.F, state_poly_3_opening_at_z: FieldR.F, state_poly_3_opening_at_z_omega: FieldR.F, gate_selector_0_opening_at_z: FieldR.F, copy_permutation_poly_0_opening_at_z: FieldR.F, copy_permutation_poly_1_opening_at_z: FieldR.F, copy_permutation_poly_2_opening_at_z: FieldR.F, copy_permutation_grand_product_opening_at_z_omega: FieldR.F, lookup_s_poly_opening_at_z_omega: FieldR.F, lookup_grand_product_opening_at_z_omega: FieldR.F, lookup_t_poly_opening_at_z: FieldR.F, lookup_t_poly_opening_at_z_omega: FieldR.F, lookup_selector_poly_opening_at_z: FieldR.F, lookup_table_type_poly_opening_at_z: FieldR.F, quotient_poly_opening_at_z: FieldR.F, linearisation_poly_opening_at_z: FieldR.F, opening_proof_at_z: g, opening_proof_at_z_omega: g, recursive_proof_length_in_words: int, vk_recursive_flag: bool, recursive_part_p1: g, recursive_part_p2: g) = {
  var ret_recursive_part_p1, ret_recursive_part_p2: g option;
  var isValid: bool;
  var ret;
    isValid <- public_input_length_in_words = 1;
    isValid <- isValid /\ (proof_length_in_words = 44);
    if (vk_recursive_flag) {
      isValid <- isValid /\ (recursive_proof_length_in_words = 4);
      ret_recursive_part_p1 <- Some recursive_part_p1;
      ret_recursive_part_p2 <- Some recursive_part_p2;
    } else {
      isValid <- isValid /\ (recursive_proof_length_in_words = 0);
      ret_recursive_part_p1 <- None;
      ret_recursive_part_p2 <- None;
    }

    if (isValid) {
      ret <- Some (
        FieldR.inF ((FieldR.asint public_input) %% 2^253),
        state_poly_0,
        state_poly_1,
        state_poly_2,
        state_poly_3,
        copy_permutation_grand_product,
        lookup_s_poly,
        lookup_grand_product,
        quotient_poly_part_0,
        quotient_poly_part_1,
        quotient_poly_part_2,
        quotient_poly_part_3,
        state_poly_0_opening_at_z,
        state_poly_1_opening_at_z,
        state_poly_2_opening_at_z,
        state_poly_3_opening_at_z,
        state_poly_3_opening_at_z_omega,
        gate_selector_0_opening_at_z,
        copy_permutation_poly_0_opening_at_z,
        copy_permutation_poly_1_opening_at_z,
        copy_permutation_poly_2_opening_at_z,
        copy_permutation_grand_product_opening_at_z_omega,
        lookup_s_poly_opening_at_z_omega,
        lookup_grand_product_opening_at_z_omega,
        lookup_t_poly_opening_at_z,
        lookup_t_poly_opening_at_z_omega,
        lookup_selector_poly_opening_at_z,
        lookup_table_type_poly_opening_at_z,
        quotient_poly_opening_at_z,
        linearisation_poly_opening_at_z,
        opening_proof_at_z,
        opening_proof_at_z_omega,
        ret_recursive_part_p1,
        ret_recursive_part_p2
      );
    } else {
      ret <- None;
    }

    return ret;
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

op point_to_uint (p: uint256*uint256) = (W256.to_uint p.`1, W256.to_uint p.`2).
op point_to_uint_mod_q (p: uint256*uint256) = ((W256.to_uint p.`1) %% Constants.Q, (W256.to_uint p.`2) %% Constants.Q).
op point_of_uint (p: int*int) = (W256.of_int p.`1, W256.of_int p.`2).

lemma on_curve_int_uint256 (x y: uint256):
  PurePrimops.eq_uint256 
    (PurePrimops.mulmod (y %% Q_MOD) (y %% Q_MOD) Q_MOD)
    (PurePrimops.addmod
      (PurePrimops.mulmod (x %% Q_MOD) (PurePrimops.mulmod (x %% Q_MOD) (x %% Q_MOD) Q_MOD) Q_MOD)
      (W256.of_int 3)
      Q_MOD
    )
  = uint256_of_bool (on_curve_int (point_to_uint (x,y))).
    proof.
    rewrite /mulmod /addmod /point_to_uint /on_curve_int /eq_uint256 /uint256_of_bool.
    progress.
    rewrite Constants.Q_int.
    have ->: (W256.to_uint (x %% Q_MOD) * W256.to_uint (x %% Q_MOD)) %% (W256.to_uint Q_MOD) =
      (W256.to_uint x * W256.to_uint x %% W256.to_uint Q_MOD).
      rewrite uint256_cast_mod.
      rewrite W256.of_uintK.
      rewrite (pmod_small _ W256.modulus).
      progress. rewrite modz_ge0. by progress.
        apply (lt_trans _ (W256.to_uint Q_MOD) _).
          exact ltz_pmod.
          by progress.
          exact modzMm.
    pose xx := (to_uint x * to_uint x %% to_uint Q_MOD).
    have ->: W256.to_uint (W256.of_int xx) = xx.
      rewrite W256.of_uintK.
      rewrite pmod_small. progress.
      rewrite /xx. exact modz_ge0.
      rewrite /xx. apply (lt_trans _ (W256.to_uint Q_MOD) _).
        exact ltz_pmod.
        by progress.
        reflexivity.
    have ->: (W256.to_uint (x %% Q_MOD) * xx %% W256.to_uint Q_MOD) =
      (W256.to_uint x * xx %% W256.to_uint Q_MOD).
      rewrite uint256_cast_mod.
      rewrite W256.of_uintK.
      rewrite (pmod_small _ W256.modulus).
       progress. rewrite modz_ge0. by progress.
        apply (lt_trans _ (W256.to_uint Q_MOD) _).
          exact ltz_pmod.
          by progress.
          exact modzMml.      
    pose xxx := (W256.to_uint x * xx %% W256.to_uint Q_MOD).
    have ->: W256.to_uint (W256.of_int xxx) = xxx.        
      rewrite W256.of_uintK.
      rewrite pmod_small. progress.
        rewrite /xxx. exact modz_ge0.
        rewrite /xxx. apply (lt_trans _ (W256.to_uint Q_MOD) _).
          exact ltz_pmod.
          by progress.
          reflexivity.
    have ->: (W256.to_uint (y %% Q_MOD) * W256.to_uint (y %% Q_MOD) %% W256.to_uint Q_MOD) =
      W256.to_uint y * W256.to_uint y %% W256.to_uint Q_MOD.
      rewrite uint256_cast_mod.
      rewrite W256.of_uintK.
      rewrite (pmod_small _ W256.modulus).
      progress. rewrite modz_ge0. by progress.
        apply (lt_trans _ (W256.to_uint Q_MOD) _).
          exact ltz_pmod.
          by progress.
          exact modzMm.
    have ->: forall (a b: int),
      0 <= a < W256.modulus =>
      0 <= b < W256.modulus =>
      (W256.of_int a = W256.of_int b) = (a = b).
      progress.
      have ->: a = W256.to_uint (W256.of_int a). rewrite W256.of_uintK. rewrite pmod_small. by progress. reflexivity.
      have ->: b = W256.to_uint (W256.of_int b). rewrite W256.of_uintK. rewrite pmod_small. by progress. reflexivity.
      simplify.
      smt.
      progress.
      exact modz_ge0.
      apply (lt_trans _ (W256.to_uint Q_MOD) _).
          exact ltz_pmod.
          by progress.
      progress.
      exact modz_ge0.
      apply (lt_trans _ (W256.to_uint Q_MOD) _).
          exact ltz_pmod.
          by progress.
      smt ().
qed.

lemma loadProof_low_equiv_mid (mem_0: mem) (recursive: bool):
    equiv [
      LoadProof.low ~ LoadProof.mid:
      !Primops.reverted{1} /\
      Primops.memory{1} = mem_0 /\
      load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
      public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
      public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
      proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
      state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
      state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
      state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
      state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
      copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
      lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
      lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
      quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
      quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
      quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
      quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
      state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
      state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
      state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
      state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
      state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
      gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
      copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
      copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
      copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
      copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
      lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
      lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
      lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
      lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
      lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
      lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
      quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
      linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
      opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
      opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
      recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
      vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
      recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
      recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2
       ==>
      (Primops.reverted{1} /\ res{2} = None) \/
      (
        !Primops.reverted{1} /\
        exists r, res{2} = Some r /\
        Primops.memory{1} = loadProof_memory_footprint
          mem_0
          recursive
          (W256.of_int r.`1)
          (point_of_uint r.`2)
          (point_of_uint r.`3)
          (point_of_uint r.`4)
          (point_of_uint r.`5)
          (point_of_uint r.`6)
          (point_of_uint r.`7)
          (point_of_uint r.`8)
          (point_of_uint r.`9)
          (point_of_uint r.`10)
          (point_of_uint r.`11)
          (point_of_uint r.`12)
          (W256.of_int r.`13)
          (W256.of_int r.`14)
          (W256.of_int r.`15)
          (W256.of_int r.`16)
          (W256.of_int r.`17)
          (W256.of_int r.`18)
          (W256.of_int r.`19)
          (W256.of_int r.`20)
          (W256.of_int r.`21)
          (W256.of_int r.`22)
          (W256.of_int r.`23)
          (W256.of_int r.`24)
          (W256.of_int r.`25)
          (W256.of_int r.`26)
          (W256.of_int r.`27)
          (W256.of_int r.`28)
          (W256.of_int r.`29)
          (W256.of_int r.`30)
          (point_of_uint r.`31)
          (point_of_uint r.`32)
          (point_of_uint (odflt (0,0) r.`33))
          (point_of_uint (odflt (0,0) r.`34))
      )    
    ].
    proof.
      proc.
      simplify.
      seq 3 1: (#pre /\ isValid{1} = uint256_of_bool isValid{2} /\ offset{1} = PurePrimops.load_calldata_offset_1).
      inline*. wp. skip. progress.
      rewrite /eq_uint256.
      rewrite -/PurePrimops.load_calldata_public_input_length.
      rewrite /uint256_of_bool.
      have H_zero: forall (x: uint256), x <> W256.one => W256.to_uint x <> 1. smt (@W256).
      smt (@W256).
      seq 4 0: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store mem_0 PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_1
      ).
      inline*. wp. skip. progress.
      congr. rewrite -/PurePrimops.load_calldata_public_input.
      rewrite /bit_and /shl.
      rewrite shlMP. exact to_uint_ge_zero.
      simplify.
      have ->:14474011154664524427946373126085988481658748083205070504932198000989141204991 = 2^253 - 1.
      by progress.
      rewrite and_mod. by progress.
      rewrite uint256_cast_mod.
      rewrite W256.of_uintK.
      rewrite (pmod_small _ W256.modulus). by progress. by progress.
      seq 1 0: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store mem_0 PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. by progress.
      seq 3 1: #pre.
      inline*. wp. skip. progress.
      rewrite /bit_and /eq_uint256 /uint256_of_bool.
      rewrite -/PurePrimops.load_calldata_proof_length.
      have H_eq_44: forall (x: uint256), x <> W256.of_int 44 => W256.to_uint x <> 44. smt (@W256).
      case (PurePrimops.load_calldata_proof_length = (W256.of_int 44)).
      progress. case (isValid{2}). progress. rewrite H1. by progress.
      by progress. progress. rewrite H_eq_44. assumption.
      by progress.
      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_state_poly_0 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_state_poly_0 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_state_poly_0 /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_state_poly_1 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_state_poly_1 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_state_poly_1/load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_state_poly_2 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_state_poly_2 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_state_poly_2 /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_state_poly_3 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_state_poly_3 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_state_poly_3 /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_copy_permutation_grand_product /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_copy_permutation_grand_product /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_copy_permutation_grand_product /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_lookup_s_poly /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_lookup_s_poly /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_lookup_s_poly /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_lookup_grand_product /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_lookup_grand_product /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_lookup_grand_product /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT (W256.of_int (quotient_poly_part_0{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT (W256.of_int (quotient_poly_part_0{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_quotient_poly_part_0 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_quotient_poly_part_0 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_quotient_poly_part_0 /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT (W256.of_int (quotient_poly_part_0{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT (W256.of_int (quotient_poly_part_0{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT (W256.of_int (quotient_poly_part_1{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT (W256.of_int (quotient_poly_part_1{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_quotient_poly_part_1 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_quotient_poly_part_1 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_quotient_poly_part_1 /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT (W256.of_int (quotient_poly_part_0{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT (W256.of_int (quotient_poly_part_0{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT (W256.of_int (quotient_poly_part_1{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT (W256.of_int (quotient_poly_part_1{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT (W256.of_int (quotient_poly_part_2{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT (W256.of_int (quotient_poly_part_2{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_quotient_poly_part_2 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_quotient_poly_part_2 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_quotient_poly_part_2 /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT (W256.of_int (quotient_poly_part_0{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT (W256.of_int (quotient_poly_part_0{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT (W256.of_int (quotient_poly_part_1{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT (W256.of_int (quotient_poly_part_1{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT (W256.of_int (quotient_poly_part_2{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT (W256.of_int (quotient_poly_part_2{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT (W256.of_int (quotient_poly_part_3{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT (W256.of_int (quotient_poly_part_3{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_quotient_poly_part_3 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_quotient_poly_part_3 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_quotient_poly_part_3 /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).
      
      seq 36 0: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT (W256.of_int (quotient_poly_part_0{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT (W256.of_int (quotient_poly_part_0{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT (W256.of_int (quotient_poly_part_1{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT (W256.of_int (quotient_poly_part_1{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT (W256.of_int (quotient_poly_part_2{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT (W256.of_int (quotient_poly_part_2{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT (W256.of_int (quotient_poly_part_3{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT (W256.of_int (quotient_poly_part_3{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (state_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (state_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (state_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT (W256.of_int (state_poly_3_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (state_poly_3_opening_at_z_omega{2} %% Constants.R)))
          PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT (W256.of_int (gate_selector_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (copy_permutation_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_s_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_t_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_t_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_selector_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_table_type_poly_opening_at_z{2} %% Constants.R)))
          PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT (W256.of_int (quotient_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT (W256.of_int (linearisation_poly_opening_at_z{2} %% Constants.R)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      do congr.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.
      rewrite Constants.R_int. rewrite uint256_cast_mod. reflexivity.

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT (W256.of_int (quotient_poly_part_0{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT (W256.of_int (quotient_poly_part_0{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT (W256.of_int (quotient_poly_part_1{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT (W256.of_int (quotient_poly_part_1{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT (W256.of_int (quotient_poly_part_2{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT (W256.of_int (quotient_poly_part_2{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT (W256.of_int (quotient_poly_part_3{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT (W256.of_int (quotient_poly_part_3{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (state_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (state_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (state_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT (W256.of_int (state_poly_3_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (state_poly_3_opening_at_z_omega{2} %% Constants.R)))
          PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT (W256.of_int (gate_selector_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (copy_permutation_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_s_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_t_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_t_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_selector_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_table_type_poly_opening_at_z{2} %% Constants.R)))
          PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT (W256.of_int (quotient_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT (W256.of_int (linearisation_poly_opening_at_z{2} %% Constants.R)))
          PROOF_OPENING_PROOF_AT_Z_X_SLOT (W256.of_int (opening_proof_at_z{2}.`1 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_Y_SLOT (W256.of_int (opening_proof_at_z{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_opening_proof_at_z /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_opening_proof_at_z /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_opening_proof_at_z /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 12 1: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT (W256.of_int (quotient_poly_part_0{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT (W256.of_int (quotient_poly_part_0{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT (W256.of_int (quotient_poly_part_1{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT (W256.of_int (quotient_poly_part_1{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT (W256.of_int (quotient_poly_part_2{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT (W256.of_int (quotient_poly_part_2{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT (W256.of_int (quotient_poly_part_3{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT (W256.of_int (quotient_poly_part_3{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (state_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (state_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (state_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT (W256.of_int (state_poly_3_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (state_poly_3_opening_at_z_omega{2} %% Constants.R)))
          PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT (W256.of_int (gate_selector_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (copy_permutation_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_s_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_t_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_t_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_selector_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_table_type_poly_opening_at_z{2} %% Constants.R)))
          PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT (W256.of_int (quotient_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT (W256.of_int (linearisation_poly_opening_at_z{2} %% Constants.R)))
          PROOF_OPENING_PROOF_AT_Z_X_SLOT (W256.of_int (opening_proof_at_z{2}.`1 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_Y_SLOT (W256.of_int (opening_proof_at_z{2}.`2 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT (W256.of_int (opening_proof_at_z_omega{2}.`1 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT (W256.of_int (opening_proof_at_z_omega{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_2
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_opening_proof_at_z_omega /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_opening_proof_at_z_omega /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_opening_proof_at_z_omega /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 3 0 : (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT (W256.of_int (quotient_poly_part_0{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT (W256.of_int (quotient_poly_part_0{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT (W256.of_int (quotient_poly_part_1{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT (W256.of_int (quotient_poly_part_1{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT (W256.of_int (quotient_poly_part_2{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT (W256.of_int (quotient_poly_part_2{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT (W256.of_int (quotient_poly_part_3{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT (W256.of_int (quotient_poly_part_3{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (state_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (state_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (state_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT (W256.of_int (state_poly_3_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (state_poly_3_opening_at_z_omega{2} %% Constants.R)))
          PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT (W256.of_int (gate_selector_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (copy_permutation_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_s_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_t_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_t_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_selector_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_table_type_poly_opening_at_z{2} %% Constants.R)))
          PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT (W256.of_int (quotient_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT (W256.of_int (linearisation_poly_opening_at_z{2} %% Constants.R)))
          PROOF_OPENING_PROOF_AT_Z_X_SLOT (W256.of_int (opening_proof_at_z{2}.`1 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_Y_SLOT (W256.of_int (opening_proof_at_z{2}.`2 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT (W256.of_int (opening_proof_at_z_omega{2}.`1 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT (W256.of_int (opening_proof_at_z_omega{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_3 /\
        recursiveProofLengthInWords{1} = PurePrimops.load_calldata_recursive_proof_length /\
        _263{1} = uint256_of_bool vk_recursive_flag{2}
      ).
      inline*. wp. skip. progress.

      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_S_POLY_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_S_POLY_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_S_POLY_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_LOOKUP_S_POLY_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_3_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_3_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_3_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_3_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_2_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_2_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_2_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_2_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_1_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_1_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_1_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_1_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_0_Y_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_0_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_0_X_SLOT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_STATE_POLYS_0_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_RECURSIVE_FLAG_SLOT).
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_PUBLIC_INPUT; progress.
        by rewrite /VK_RECURSIVE_FLAG_SLOT /PROOF_PUBLIC_INPUT; progress.
      rewrite H0.
      rewrite /uint256_of_bool /bool_of_uint256.
      smt ().
      case (vk_recursive_flag{2}).
      rcondt{2} 1. by progress.
      rcondf{1} 1. progress. skip. progress. rewrite H1. rewrite /uint256_of_bool. progress. smt ().
      
      seq 2 1: (#pre /\ recursive /\ vk_recursive_flag{2}).
      wp. skip. progress.
      have H_four: forall (x: uint256), x <> W256.of_int 4 => W256.to_uint x <> 4. smt (@W256).
      rewrite /bit_and /eq_uint256 /uint256_of_bool.
      case (PurePrimops.load_calldata_recursive_proof_length = (W256.of_int 4)).
      progress. rewrite H2. progress. case (isValid{2}). by progress. by progress.
      progress. rewrite H_four. assumption. case (isValid{2}). by progress. by progress.
      rewrite H0 in H1.
      rewrite /bool_of_uint256 /uint256_of_bool in H1.
      case recursive. by progress.
      move => H_rec. have H2 := H1. rewrite H_rec in H2. smt (@W256).

      seq 12 1 : (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT (W256.of_int (quotient_poly_part_0{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT (W256.of_int (quotient_poly_part_0{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT (W256.of_int (quotient_poly_part_1{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT (W256.of_int (quotient_poly_part_1{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT (W256.of_int (quotient_poly_part_2{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT (W256.of_int (quotient_poly_part_2{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT (W256.of_int (quotient_poly_part_3{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT (W256.of_int (quotient_poly_part_3{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (state_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (state_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (state_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT (W256.of_int (state_poly_3_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (state_poly_3_opening_at_z_omega{2} %% Constants.R)))
          PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT (W256.of_int (gate_selector_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (copy_permutation_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_s_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_t_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_t_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_selector_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_table_type_poly_opening_at_z{2} %% Constants.R)))
          PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT (W256.of_int (quotient_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT (W256.of_int (linearisation_poly_opening_at_z{2} %% Constants.R)))
          PROOF_OPENING_PROOF_AT_Z_X_SLOT (W256.of_int (opening_proof_at_z{2}.`1 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_Y_SLOT (W256.of_int (opening_proof_at_z{2}.`2 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT (W256.of_int (opening_proof_at_z_omega{2}.`1 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT (W256.of_int (opening_proof_at_z_omega{2}.`2 %% Constants.Q)))
          PROOF_RECURSIVE_PART_P1_X_SLOT (W256.of_int (recursive_part_p1{2}.`1 %% Constants.Q)))
          PROOF_RECURSIVE_PART_P1_Y_SLOT (W256.of_int (recursive_part_p1{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_3 /\
        recursiveProofLengthInWords{1} = PurePrimops.load_calldata_recursive_proof_length /\
        _263{1} = uint256_of_bool vk_recursive_flag{2} /\
        vk_recursive_flag{2} /\
        recursive
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_recursive_part_p1 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_recursive_part_p1 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_recursive_part_p1 /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 0 1 : (#pre /\ ret_recursive_part_p1{2} = Some(recursive_part_p1.`1{2} %% Constants.Q, recursive_part_p1.`2{2} %% Constants.Q)).
      wp. skip. by progress.

      seq 13 1 : (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
          PROOF_PUBLIC_INPUT (PurePrimops.load_calldata_public_input %% W256.of_int (2^253)))
          PROOF_STATE_POLYS_0_X_SLOT (W256.of_int (state_poly_0{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_0_Y_SLOT (W256.of_int (state_poly_0{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_1_X_SLOT (W256.of_int (state_poly_1{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_1_Y_SLOT (W256.of_int (state_poly_1{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_2_X_SLOT (W256.of_int (state_poly_2{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_2_Y_SLOT (W256.of_int (state_poly_2{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_3_X_SLOT (W256.of_int (state_poly_3{2}.`1 %% Constants.Q)))
          PROOF_STATE_POLYS_3_Y_SLOT (W256.of_int (state_poly_3{2}.`2 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT (W256.of_int (copy_permutation_grand_product{2}.`1 %% Constants.Q)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT (W256.of_int (copy_permutation_grand_product{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_X_SLOT (W256.of_int (lookup_s_poly{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_S_POLY_Y_SLOT (W256.of_int (lookup_s_poly{2}.`2 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT (W256.of_int (lookup_grand_product{2}.`1 %% Constants.Q)))
          PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT (W256.of_int (lookup_grand_product{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT (W256.of_int (quotient_poly_part_0{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT (W256.of_int (quotient_poly_part_0{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT (W256.of_int (quotient_poly_part_1{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT (W256.of_int (quotient_poly_part_1{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT (W256.of_int (quotient_poly_part_2{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT (W256.of_int (quotient_poly_part_2{2}.`2 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT (W256.of_int (quotient_poly_part_3{2}.`1 %% Constants.Q)))
          PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT (W256.of_int (quotient_poly_part_3{2}.`2 %% Constants.Q)))
          PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (state_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (state_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (state_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT (W256.of_int (state_poly_3_opening_at_z{2} %% Constants.R)))
          PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (state_poly_3_opening_at_z_omega{2} %% Constants.R)))
          PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT (W256.of_int (gate_selector_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_0_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_1_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT (W256.of_int (copy_permutation_poly_2_opening_at_z{2} %% Constants.R)))
          PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (copy_permutation_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_s_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_grand_product_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_t_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT (W256.of_int (lookup_t_poly_opening_at_z_omega{2} %% Constants.R)))
          PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_selector_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT (W256.of_int (lookup_table_type_poly_opening_at_z{2} %% Constants.R)))
          PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT (W256.of_int (quotient_poly_opening_at_z{2} %% Constants.R)))
          PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT (W256.of_int (linearisation_poly_opening_at_z{2} %% Constants.R)))
          PROOF_OPENING_PROOF_AT_Z_X_SLOT (W256.of_int (opening_proof_at_z{2}.`1 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_Y_SLOT (W256.of_int (opening_proof_at_z{2}.`2 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT (W256.of_int (opening_proof_at_z_omega{2}.`1 %% Constants.Q)))
          PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT (W256.of_int (opening_proof_at_z_omega{2}.`2 %% Constants.Q)))
          PROOF_RECURSIVE_PART_P1_X_SLOT (W256.of_int (recursive_part_p1{2}.`1 %% Constants.Q)))
          PROOF_RECURSIVE_PART_P1_Y_SLOT (W256.of_int (recursive_part_p1{2}.`2 %% Constants.Q)))
          PROOF_RECURSIVE_PART_P2_X_SLOT (W256.of_int (recursive_part_p2{2}.`1 %% Constants.Q)))
          PROOF_RECURSIVE_PART_P2_Y_SLOT (W256.of_int (recursive_part_p2{2}.`2 %% Constants.Q)) /\
        load mem_0 VK_RECURSIVE_FLAG_SLOT = uint256_of_bool recursive /\
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        vk_recursive_flag{2} = bool_of_uint256 (load mem_0 VK_RECURSIVE_FLAG_SLOT) /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        isValid{1} = uint256_of_bool isValid{2} /\
        offset{1} = PurePrimops.load_calldata_offset_3 /\
        recursiveProofLengthInWords{1} = PurePrimops.load_calldata_recursive_proof_length /\
        _263{1} = uint256_of_bool vk_recursive_flag{2} /\
        ret_recursive_part_p1{2} = Some(recursive_part_p1.`1{2} %% Constants.Q, recursive_part_p1.`2{2} %% Constants.Q) /\
        vk_recursive_flag{2} /\
        recursive
      ).
      inline*. wp. skip. progress.
      congr. congr. rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_recursive_part_p2 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite /point_to_uint. simplify.
      rewrite /PurePrimops.load_calldata_recursive_part_p2 /load_pair.
      simplify.
      rewrite uint256_cast_mod.
      rewrite Constants.Q_int.
      reflexivity.

      rewrite on_curve_int_uint256.
      rewrite /point_to_uint /PurePrimops.load_calldata_recursive_part_p2 /load_pair.
      rewrite /bit_and /uint256_of_bool.
      simplify.
      smt (@W256).

      seq 0 1 : (#pre /\ ret_recursive_part_p2{2} = Some(recursive_part_p2.`1{2} %% Constants.Q, recursive_part_p2.`2{2} %% Constants.Q)).
      wp. skip. by progress.

      case (isValid{2}).
      rcondt{2} 1. by progress.
      rcondf{1} 1. progress. skip. progress. rewrite /bool_of_uint256 /iszero /uint256_of_bool. progress. smt (@W256).
      wp. skip. progress.
      exists (
        W256.to_uint PurePrimops.load_calldata_public_input %% 2^253,
        point_to_uint_mod_q PurePrimops.load_calldata_state_poly_0,
        point_to_uint_mod_q PurePrimops.load_calldata_state_poly_1,
        point_to_uint_mod_q PurePrimops.load_calldata_state_poly_2,
        point_to_uint_mod_q PurePrimops.load_calldata_state_poly_3,
        point_to_uint_mod_q PurePrimops.load_calldata_copy_permutation_grand_product,
        point_to_uint_mod_q PurePrimops.load_calldata_lookup_s_poly,
        point_to_uint_mod_q PurePrimops.load_calldata_lookup_grand_product,
        point_to_uint_mod_q PurePrimops.load_calldata_quotient_poly_part_0,
        point_to_uint_mod_q PurePrimops.load_calldata_quotient_poly_part_1,
        point_to_uint_mod_q PurePrimops.load_calldata_quotient_poly_part_2,
        point_to_uint_mod_q PurePrimops.load_calldata_quotient_poly_part_3,
        W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z %% Constants.R,
        point_to_uint_mod_q PurePrimops.load_calldata_opening_proof_at_z,
        point_to_uint_mod_q PurePrimops.load_calldata_opening_proof_at_z_omega,
        Some(point_to_uint_mod_q PurePrimops.load_calldata_recursive_part_p1),
        Some(point_to_uint_mod_q PurePrimops.load_calldata_recursive_part_p2)
      ). progress.
      rewrite /loadProof_memory_footprint. progress.
      rewrite H2. progress.
      pose mem_1 := store mem_0 _ _.
      pose mem_1' := store mem_0 _ _.
      have ->: mem_1' = mem_1. rewrite /mem_1 /mem_1'. rewrite uint256_cast_mod W256.of_uintK. by progress.
      do 15! have ->: forall (x), W256.of_int ((point_to_uint x).`1 %% Constants.Q) = (point_of_uint(point_to_uint_mod_q x)).`1 by progress.
      do 15! have ->: forall (x), W256.of_int ((point_to_uint x).`2 %% Constants.Q) = (point_of_uint(point_to_uint_mod_q x)).`2 by progress.
      reflexivity.


      (*!isValid{2}*)
      rcondf{2} 1. by progress.
      rcondt{1} 1. progress. skip. progress. rewrite H3 /uint256_of_bool /iszero /bool_of_uint256. progress. smt (@W256).
      call{1} revertWithMessage_low_pspec. wp. skip. by progress.

      (*!recursive*)
      rcondf{2} 1. by progress.
      rcondt{1} 1. progress. skip. progress. rewrite H1. by progress.
      seq 2 3: (#pre /\ !recursive /\ ret_recursive_part_p1{2} = None /\ ret_recursive_part_p2{2} = None).
      wp. skip. progress.
      rewrite /bit_and /iszero /uint256_of_bool.
      have H_zero: forall (x: uint256), x <> W256.zero => W256.to_uint x <> 0. smt (@W256).
      case (PurePrimops.load_calldata_recursive_proof_length = W256.zero).
      progress. rewrite H2. progress. case (isValid{2}). by progress. by progress.
      progress. rewrite H_zero. assumption. case (isValid{2}). by progress. by progress.
      rewrite H0 in H1.
      rewrite /bool_of_uint256 /uint256_of_bool in H1.
      case recursive. move => H_rec. have H2 := H1. rewrite H_rec in H2. smt (@W256).
      by progress.

      case (isValid{2}).
      rcondt{2} 1. by progress.
      rcondf{1} 1. progress. skip. progress. rewrite H3 /uint256_of_bool /iszero /bool_of_uint256. progress. smt (@W256).
      wp. skip. progress.
      exists (
        W256.to_uint PurePrimops.load_calldata_public_input %% 2^253,
        point_to_uint_mod_q PurePrimops.load_calldata_state_poly_0,
        point_to_uint_mod_q PurePrimops.load_calldata_state_poly_1,
        point_to_uint_mod_q PurePrimops.load_calldata_state_poly_2,
        point_to_uint_mod_q PurePrimops.load_calldata_state_poly_3,
        point_to_uint_mod_q PurePrimops.load_calldata_copy_permutation_grand_product,
        point_to_uint_mod_q PurePrimops.load_calldata_lookup_s_poly,
        point_to_uint_mod_q PurePrimops.load_calldata_lookup_grand_product,
        point_to_uint_mod_q PurePrimops.load_calldata_quotient_poly_part_0,
        point_to_uint_mod_q PurePrimops.load_calldata_quotient_poly_part_1,
        point_to_uint_mod_q PurePrimops.load_calldata_quotient_poly_part_2,
        point_to_uint_mod_q PurePrimops.load_calldata_quotient_poly_part_3,
        W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z %% Constants.R,
        W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z %% Constants.R,
        point_to_uint_mod_q PurePrimops.load_calldata_opening_proof_at_z,
        point_to_uint_mod_q PurePrimops.load_calldata_opening_proof_at_z_omega,
        None,
        None
      ). progress.
      rewrite /loadProof_memory_footprint. progress.
      rewrite H2. progress.
      pose mem_1 := store mem_0 _ _.
      pose mem_1' := store mem_0 _ _.
      have ->: mem_1' = mem_1. rewrite /mem_1 /mem_1'. rewrite uint256_cast_mod W256.of_uintK. by progress.
      do 13! have ->: forall (x), W256.of_int ((point_to_uint x).`1 %% Constants.Q) = (point_of_uint(point_to_uint_mod_q x)).`1 by progress.
      do 13! have ->: forall (x), W256.of_int ((point_to_uint x).`2 %% Constants.Q) = (point_of_uint(point_to_uint_mod_q x)).`2 by progress.
      reflexivity.


      (*!isValid{2}*)
      rcondf{2} 1. by progress.
      rcondt{1} 1. progress. skip. progress. rewrite H3 /uint256_of_bool /iszero /bool_of_uint256. progress. smt (@W256).
      call{1} revertWithMessage_low_pspec. wp. skip. by progress.
qed.

lemma on_curve_int_of_cast (p: g): on_curve_int(F_to_int_point(aspoint_G1 p)).
    proof.
      have H_on_curve := aspoint_on_curve p.
      rewrite /on_curve in H_on_curve.
      rewrite /on_curve_int /F_to_int_point. simplify.
      rewrite Constants.q_eq_fieldq_p.
      rewrite FieldQ.eq_inF.
      pose lhs := FieldQ.inF(_ + 3).
      rewrite FieldQ.inF_mod.
      rewrite -FieldQ.mulE.
      rewrite H_on_curve.
      rewrite FieldQ.addE.
      rewrite FieldQ.mulE.
      rewrite FieldQ.mulE.
      rewrite /lhs.
      rewrite FieldQ.inFK.
      rewrite FieldQ.inF_mod.
      rewrite modzDmr.
      reflexivity.
qed.

lemma loadProof_mid_equiv_high (recursive: bool):
    equiv [
      LoadProof.mid ~ LoadProof.high:
      ={public_input_length_in_words, proof_length_in_words, vk_recursive_flag, recursive_proof_length_in_words} /\
      vk_recursive_flag{1} = recursive /\
      public_input{1} = FieldR.asint public_input{2} /\
      state_poly_0{1} = F_to_int_point (aspoint_G1 state_poly_0{2}) /\
      state_poly_1{1} = F_to_int_point (aspoint_G1 state_poly_1{2}) /\
      state_poly_2{1} = F_to_int_point (aspoint_G1 state_poly_2{2}) /\
      state_poly_3{1} = F_to_int_point (aspoint_G1 state_poly_3{2}) /\
      copy_permutation_grand_product{1} = F_to_int_point (aspoint_G1 copy_permutation_grand_product{2}) /\
      lookup_s_poly{1} = F_to_int_point (aspoint_G1 lookup_s_poly{2}) /\
      lookup_grand_product{1} = F_to_int_point (aspoint_G1 lookup_grand_product{2}) /\
      quotient_poly_part_0{1} = F_to_int_point (aspoint_G1 quotient_poly_part_0{2}) /\
      quotient_poly_part_1{1} = F_to_int_point (aspoint_G1 quotient_poly_part_1{2}) /\
      quotient_poly_part_2{1} = F_to_int_point (aspoint_G1 quotient_poly_part_2{2}) /\
      quotient_poly_part_3{1} = F_to_int_point (aspoint_G1 quotient_poly_part_3{2}) /\
      state_poly_0_opening_at_z{1} = FieldR.asint state_poly_0_opening_at_z{2} /\
      state_poly_1_opening_at_z{1} = FieldR.asint state_poly_1_opening_at_z{2} /\
      state_poly_2_opening_at_z{1} = FieldR.asint state_poly_2_opening_at_z{2} /\
      state_poly_3_opening_at_z{1} = FieldR.asint state_poly_3_opening_at_z{2} /\
      state_poly_3_opening_at_z_omega{1} = FieldR.asint state_poly_3_opening_at_z_omega{2} /\
      gate_selector_0_opening_at_z{1} = FieldR.asint gate_selector_0_opening_at_z{2} /\
      copy_permutation_poly_0_opening_at_z{1} = FieldR.asint copy_permutation_poly_0_opening_at_z{2} /\
      copy_permutation_poly_1_opening_at_z{1} = FieldR.asint copy_permutation_poly_1_opening_at_z{2} /\
      copy_permutation_poly_2_opening_at_z{1} = FieldR.asint copy_permutation_poly_2_opening_at_z{2} /\
      copy_permutation_grand_product_opening_at_z_omega{1} = FieldR.asint copy_permutation_grand_product_opening_at_z_omega{2} /\
      lookup_s_poly_opening_at_z_omega{1} = FieldR.asint lookup_s_poly_opening_at_z_omega{2} /\
      lookup_grand_product_opening_at_z_omega{1} = FieldR.asint lookup_grand_product_opening_at_z_omega{2} /\
      lookup_t_poly_opening_at_z{1} = FieldR.asint lookup_t_poly_opening_at_z{2} /\
      lookup_t_poly_opening_at_z_omega{1} = FieldR.asint lookup_t_poly_opening_at_z_omega{2} /\
      lookup_selector_poly_opening_at_z{1} = FieldR.asint lookup_selector_poly_opening_at_z{2} /\
      lookup_table_type_poly_opening_at_z{1} = FieldR.asint lookup_table_type_poly_opening_at_z{2} /\
      quotient_poly_opening_at_z{1} = FieldR.asint quotient_poly_opening_at_z{2} /\
      linearisation_poly_opening_at_z{1} = FieldR.asint linearisation_poly_opening_at_z{2} /\
      opening_proof_at_z{1} = F_to_int_point (aspoint_G1 opening_proof_at_z{2}) /\
      opening_proof_at_z_omega{1} = F_to_int_point (aspoint_G1 opening_proof_at_z_omega{2}) /\
      recursive_part_p1{1} = F_to_int_point (aspoint_G1 recursive_part_p1{2}) /\
      recursive_part_p2{1} = F_to_int_point (aspoint_G1 recursive_part_p2{2})
       ==>
      (res{1} = None /\ res{2} = None) \/
      (
        exists r1 r2,  res{1} = Some r1 /\ res{2} = Some r2 /\
          r1.`1 = FieldR.asint r2.`1 /\
          r1.`2 = F_to_int_point (aspoint_G1 r2.`2) /\ 
          r1.`3 = F_to_int_point (aspoint_G1 r2.`3) /\
          r1.`4 = F_to_int_point (aspoint_G1 r2.`4) /\
          r1.`5 = F_to_int_point (aspoint_G1 r2.`5) /\
          r1.`6 = F_to_int_point (aspoint_G1 r2.`6) /\
          r1.`7 = F_to_int_point (aspoint_G1 r2.`7) /\
          r1.`8 = F_to_int_point (aspoint_G1 r2.`8) /\
          r1.`9 = F_to_int_point (aspoint_G1 r2.`9) /\
          r1.`10 = F_to_int_point (aspoint_G1 r2.`10) /\
          r1.`11 = F_to_int_point (aspoint_G1 r2.`11) /\
          r1.`12 = F_to_int_point (aspoint_G1 r2.`12) /\
          r1.`13 = FieldR.asint r2.`13 /\
          r1.`14 = FieldR.asint r2.`14 /\
          r1.`15 = FieldR.asint r2.`15 /\
          r1.`16 = FieldR.asint r2.`16 /\
          r1.`17 = FieldR.asint r2.`17 /\
          r1.`18 = FieldR.asint r2.`18 /\
          r1.`19 = FieldR.asint r2.`19 /\
          r1.`20 = FieldR.asint r2.`20 /\
          r1.`21 = FieldR.asint r2.`21 /\
          r1.`22 = FieldR.asint r2.`22 /\
          r1.`23 = FieldR.asint r2.`23 /\
          r1.`24 = FieldR.asint r2.`24 /\
          r1.`25 = FieldR.asint r2.`25 /\
          r1.`26 = FieldR.asint r2.`26 /\
          r1.`27 = FieldR.asint r2.`27 /\
          r1.`28 = FieldR.asint r2.`28 /\
          r1.`29 = FieldR.asint r2.`29 /\
          r1.`30 = FieldR.asint r2.`30 /\
          r1.`31 = F_to_int_point (aspoint_G1 r2.`31) /\
          r1.`32 = F_to_int_point (aspoint_G1 r2.`32) /\
          r1.`33 = omap F_to_int_point (omap aspoint_G1 r2.`33) /\
          r1.`34 = omap F_to_int_point (omap aspoint_G1 r2.`34)
      )    
    ].
    proof.
      proc.
      simplify. 
      seq 15 2 : (#pre /\ ={isValid}).
      wp. skip.
      progress.
      do rewrite on_curve_int_of_cast. by progress.
      case recursive.
      rcondt{1} 1. by progress. 
      rcondt{2} 1. by progress.

      seq 5 3 : (
        #pre /\
        ret_recursive_part_p1{1} = omap F_to_int_point (omap aspoint_G1 ret_recursive_part_p1{2}) /\
        ret_recursive_part_p2{1} = omap F_to_int_point (omap aspoint_G1 ret_recursive_part_p2{2})
      ).
      wp. skip. progress. do rewrite on_curve_int_of_cast. by progress.
      rewrite Constants.q_eq_fieldq_p. rewrite F_to_int_point_mod_Q_1. rewrite F_to_int_point_mod_Q_2. by progress.
      rewrite Constants.q_eq_fieldq_p. rewrite F_to_int_point_mod_Q_1. rewrite F_to_int_point_mod_Q_2. by progress.
     
      exists* isValid{1}. elim*=> isValid_L.
      case isValid_L. rcondt{1} 1. by progress.
      rcondt{2} 1. by progress. wp. skip. progress.
      have H_point: forall (p: g), ((F_to_int_point (aspoint_G1 p)).`1 %% Constants.Q, (F_to_int_point (aspoint_G1 p)).`2 %% Constants.Q) = F_to_int_point (aspoint_G1 p).
        progress.
        rewrite Constants.q_eq_fieldq_p.
        rewrite F_to_int_point_mod_Q_1 F_to_int_point_mod_Q_2.
        by progress.
      do rewrite H_point.
      rewrite Constants.r_eq_fieldr_p.
      have H_mod: forall (r: FieldR.F), (FieldR.asint r) %% FieldR.p = FieldR.asint r.
        progress.
        rewrite pmod_small.
        progress.
        exact FieldR.ge0_asint.
        exact FieldR.gtp_asint.
        reflexivity.
      do rewrite H_mod.
      exists (
        (FieldR.asint public_input{2}) %% 14474011154664524427946373126085988481658748083205070504932198000989141204992,
        F_to_int_point (aspoint_G1 state_poly_0{2}),
        F_to_int_point (aspoint_G1 state_poly_1{2}),
        F_to_int_point (aspoint_G1 state_poly_2{2}),
        F_to_int_point (aspoint_G1 state_poly_3{2}),
        F_to_int_point (aspoint_G1 copy_permutation_grand_product{2}),
        F_to_int_point (aspoint_G1 lookup_s_poly{2}),
        F_to_int_point (aspoint_G1 lookup_grand_product{2}),
        F_to_int_point (aspoint_G1 quotient_poly_part_0{2}),
        F_to_int_point (aspoint_G1 quotient_poly_part_1{2}),
        F_to_int_point (aspoint_G1 quotient_poly_part_2{2}),
        F_to_int_point (aspoint_G1 quotient_poly_part_3{2}),
        FieldR.asint state_poly_0_opening_at_z{2},
        FieldR.asint state_poly_1_opening_at_z{2},
        FieldR.asint state_poly_2_opening_at_z{2},
        FieldR.asint state_poly_3_opening_at_z{2},
        FieldR.asint state_poly_3_opening_at_z_omega{2},
        FieldR.asint gate_selector_0_opening_at_z{2},
        FieldR.asint copy_permutation_poly_0_opening_at_z{2},
        FieldR.asint copy_permutation_poly_1_opening_at_z{2},
        FieldR.asint copy_permutation_poly_2_opening_at_z{2},
        FieldR.asint copy_permutation_grand_product_opening_at_z_omega{2},
        FieldR.asint lookup_s_poly_opening_at_z_omega{2},
        FieldR.asint lookup_grand_product_opening_at_z_omega{2},
        FieldR.asint lookup_t_poly_opening_at_z{2},
        FieldR.asint lookup_t_poly_opening_at_z_omega{2},
        FieldR.asint lookup_selector_poly_opening_at_z{2},
        FieldR.asint lookup_table_type_poly_opening_at_z{2},
        FieldR.asint quotient_poly_opening_at_z{2},
        FieldR.asint linearisation_poly_opening_at_z{2},
        F_to_int_point (aspoint_G1 opening_proof_at_z{2}),
        F_to_int_point (aspoint_G1 opening_proof_at_z_omega{2}),
        omap F_to_int_point (omap aspoint_G1 ret_recursive_part_p1{2}),
        omap F_to_int_point (omap aspoint_G1 ret_recursive_part_p2{2})
      ).
      simplify.
      exists (
        FieldR.inF ((FieldR.asint public_input{2}) %% 14474011154664524427946373126085988481658748083205070504932198000989141204992),
        state_poly_0{2}, state_poly_1{2}, state_poly_2{2}, state_poly_3{2},
        copy_permutation_grand_product{2}, lookup_s_poly{2},
        lookup_grand_product{2}, quotient_poly_part_0{2}, quotient_poly_part_1{2},
        quotient_poly_part_2{2}, quotient_poly_part_3{2},
        state_poly_0_opening_at_z{2}, state_poly_1_opening_at_z{2},
        state_poly_2_opening_at_z{2}, state_poly_3_opening_at_z{2},
        state_poly_3_opening_at_z_omega{2}, gate_selector_0_opening_at_z{2},
        copy_permutation_poly_0_opening_at_z{2},
        copy_permutation_poly_1_opening_at_z{2},
        copy_permutation_poly_2_opening_at_z{2},
        copy_permutation_grand_product_opening_at_z_omega{2},
        lookup_s_poly_opening_at_z_omega{2},
        lookup_grand_product_opening_at_z_omega{2}, lookup_t_poly_opening_at_z{2},
        lookup_t_poly_opening_at_z_omega{2}, lookup_selector_poly_opening_at_z{2},
        lookup_table_type_poly_opening_at_z{2}, quotient_poly_opening_at_z{2},
        linearisation_poly_opening_at_z{2}, opening_proof_at_z{2},
        opening_proof_at_z_omega{2}, ret_recursive_part_p1{2},
        ret_recursive_part_p2{2}
      ).
      progress.
      rewrite FieldR.inFK.
      rewrite -Constants.r_eq_fieldr_p.
      rewrite (pmod_small _ Constants.R).
      progress.
      exact modz_ge0.
      apply (int_lt_lt_trans _ 14474011154664524427946373126085988481658748083205070504932198000989141204992).
      exact ltz_pmod.
      rewrite /Constants.R. by trivial.
      reflexivity.


      rcondf{1} 1. by progress. 
      rcondf{2} 1. by progress. 
      wp. skip. by progress. 
      rcondf{1} 1. by progress. 
      rcondf{2} 1. by progress. 

      seq 3 3: (
        #pre /\
        ret_recursive_part_p1{1} = omap F_to_int_point (omap aspoint_G1 ret_recursive_part_p1{2}) /\
        ret_recursive_part_p2{1} = omap F_to_int_point (omap aspoint_G1 ret_recursive_part_p2{2})
      ).
      wp. skip. by progress.

      case (!isValid{2}).
      rcondf{2} 1. by progress.
      rcondf{1} 1. by progress.
      wp. skip. by progress.

      (* case isValid{2}*)
      rcondt{2} 1. by progress.
      rcondt{1} 1. by progress.
      wp. skip. progress.
      have H_point: forall (p: g), ((F_to_int_point (aspoint_G1 p)).`1 %% Constants.Q, (F_to_int_point (aspoint_G1 p)).`2 %% Constants.Q) = F_to_int_point (aspoint_G1 p).
        progress.
        rewrite Constants.q_eq_fieldq_p.
        rewrite F_to_int_point_mod_Q_1 F_to_int_point_mod_Q_2.
        by progress.
      do rewrite H_point.
      rewrite Constants.r_eq_fieldr_p.
      have H_mod: forall (r: FieldR.F), (FieldR.asint r) %% FieldR.p = FieldR.asint r.
        progress.
        rewrite pmod_small.
        progress.
        exact FieldR.ge0_asint.
        exact FieldR.gtp_asint.
        reflexivity.
      do rewrite H_mod.
      exists (
        (FieldR.asint public_input{2}) %% 14474011154664524427946373126085988481658748083205070504932198000989141204992,
        F_to_int_point (aspoint_G1 state_poly_0{2}),
        F_to_int_point (aspoint_G1 state_poly_1{2}),
        F_to_int_point (aspoint_G1 state_poly_2{2}),
        F_to_int_point (aspoint_G1 state_poly_3{2}),
        F_to_int_point (aspoint_G1 copy_permutation_grand_product{2}),
        F_to_int_point (aspoint_G1 lookup_s_poly{2}),
        F_to_int_point (aspoint_G1 lookup_grand_product{2}),
        F_to_int_point (aspoint_G1 quotient_poly_part_0{2}),
        F_to_int_point (aspoint_G1 quotient_poly_part_1{2}),
        F_to_int_point (aspoint_G1 quotient_poly_part_2{2}),
        F_to_int_point (aspoint_G1 quotient_poly_part_3{2}),
        FieldR.asint state_poly_0_opening_at_z{2},
        FieldR.asint state_poly_1_opening_at_z{2},
        FieldR.asint state_poly_2_opening_at_z{2},
        FieldR.asint state_poly_3_opening_at_z{2},
        FieldR.asint state_poly_3_opening_at_z_omega{2},
        FieldR.asint gate_selector_0_opening_at_z{2},
        FieldR.asint copy_permutation_poly_0_opening_at_z{2},
        FieldR.asint copy_permutation_poly_1_opening_at_z{2},
        FieldR.asint copy_permutation_poly_2_opening_at_z{2},
        FieldR.asint copy_permutation_grand_product_opening_at_z_omega{2},
        FieldR.asint lookup_s_poly_opening_at_z_omega{2},
        FieldR.asint lookup_grand_product_opening_at_z_omega{2},
        FieldR.asint lookup_t_poly_opening_at_z{2},
        FieldR.asint lookup_t_poly_opening_at_z_omega{2},
        FieldR.asint lookup_selector_poly_opening_at_z{2},
        FieldR.asint lookup_table_type_poly_opening_at_z{2},
        FieldR.asint quotient_poly_opening_at_z{2},
        FieldR.asint linearisation_poly_opening_at_z{2},
        F_to_int_point (aspoint_G1 opening_proof_at_z{2}),
        F_to_int_point (aspoint_G1 opening_proof_at_z_omega{2}),
        omap F_to_int_point (omap aspoint_G1 ret_recursive_part_p1{2}),
        omap F_to_int_point (omap aspoint_G1 ret_recursive_part_p2{2})
      ).
      simplify.
      exists (
        FieldR.inF ((FieldR.asint public_input{2}) %% 14474011154664524427946373126085988481658748083205070504932198000989141204992),
        state_poly_0{2}, state_poly_1{2}, state_poly_2{2}, state_poly_3{2},
        copy_permutation_grand_product{2}, lookup_s_poly{2},
        lookup_grand_product{2}, quotient_poly_part_0{2}, quotient_poly_part_1{2},
        quotient_poly_part_2{2}, quotient_poly_part_3{2},
        state_poly_0_opening_at_z{2}, state_poly_1_opening_at_z{2},
        state_poly_2_opening_at_z{2}, state_poly_3_opening_at_z{2},
        state_poly_3_opening_at_z_omega{2}, gate_selector_0_opening_at_z{2},
        copy_permutation_poly_0_opening_at_z{2},
        copy_permutation_poly_1_opening_at_z{2},
        copy_permutation_poly_2_opening_at_z{2},
        copy_permutation_grand_product_opening_at_z_omega{2},
        lookup_s_poly_opening_at_z_omega{2},
        lookup_grand_product_opening_at_z_omega{2}, lookup_t_poly_opening_at_z{2},
        lookup_t_poly_opening_at_z_omega{2}, lookup_selector_poly_opening_at_z{2},
        lookup_table_type_poly_opening_at_z{2}, quotient_poly_opening_at_z{2},
        linearisation_poly_opening_at_z{2}, opening_proof_at_z{2},
        opening_proof_at_z_omega{2}, ret_recursive_part_p1{2},
        ret_recursive_part_p2{2}
      ).
      progress.
      rewrite FieldR.inFK.
      rewrite -Constants.r_eq_fieldr_p.
      rewrite (pmod_small _ Constants.R).
      progress.
      exact modz_ge0.
      apply (int_lt_lt_trans _ 14474011154664524427946373126085988481658748083205070504932198000989141204992).
      exact ltz_pmod.
      rewrite /Constants.R. by trivial.
      reflexivity.
qed.
