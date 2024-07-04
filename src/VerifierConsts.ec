require import UInt256.

op VK_GATE_SETUP_0_X_SLOT : uint256 = W256.of_int (512 + 0).
op VK_GATE_SETUP_0_Y_SLOT : uint256 = W256.of_int (512 + 32).
op VK_GATE_SETUP_1_X_SLOT : uint256 = W256.of_int (512 + 64).
op VK_GATE_SETUP_1_Y_SLOT : uint256 = W256.of_int (512 + 96).
op VK_GATE_SETUP_2_X_SLOT : uint256 = W256.of_int (512 + 128).
op VK_GATE_SETUP_2_Y_SLOT : uint256 = W256.of_int (512 + 160).
op VK_GATE_SETUP_3_X_SLOT : uint256 = W256.of_int (512 + 192).
op VK_GATE_SETUP_3_Y_SLOT : uint256 = W256.of_int (512 + 224).
op VK_GATE_SETUP_4_X_SLOT : uint256 = W256.of_int (512 + 256).
op VK_GATE_SETUP_4_Y_SLOT : uint256 = W256.of_int (512 + 288).
op VK_GATE_SETUP_5_X_SLOT : uint256 = W256.of_int (512 + 320).
op VK_GATE_SETUP_5_Y_SLOT : uint256 = W256.of_int (512 + 352).
op VK_GATE_SETUP_6_X_SLOT : uint256 = W256.of_int (512 + 384).
op VK_GATE_SETUP_6_Y_SLOT : uint256 = W256.of_int (512 + 416).
op VK_GATE_SETUP_7_X_SLOT : uint256 = W256.of_int (512 + 448).
op VK_GATE_SETUP_7_Y_SLOT : uint256 = W256.of_int (512 + 480).

op VK_GATE_SELECTORS_0_X_SLOT : uint256 = W256.of_int (512 + 512).
op VK_GATE_SELECTORS_0_Y_SLOT : uint256 = W256.of_int (512 + 544).
op VK_GATE_SELECTORS_1_X_SLOT : uint256 = W256.of_int (512 + 576).
op VK_GATE_SELECTORS_1_Y_SLOT : uint256 = W256.of_int (512 + 608).

op VK_PERMUTATION_0_X_SLOT : uint256 = W256.of_int (512 + 640).
op VK_PERMUTATION_0_Y_SLOT : uint256 = W256.of_int (512 + 672).
op VK_PERMUTATION_1_X_SLOT : uint256 = W256.of_int (512 + 704).
op VK_PERMUTATION_1_Y_SLOT : uint256 = W256.of_int (512 + 736).
op VK_PERMUTATION_2_X_SLOT : uint256 = W256.of_int (512 + 768).
op VK_PERMUTATION_2_Y_SLOT : uint256 = W256.of_int (512 + 800).
op VK_PERMUTATION_3_X_SLOT : uint256 = W256.of_int (512 + 832).
op VK_PERMUTATION_3_Y_SLOT : uint256 = W256.of_int (512 + 864).

op VK_LOOKUP_SELECTOR_X_SLOT : uint256 = W256.of_int (512 + 896).
op VK_LOOKUP_SELECTOR_Y_SLOT : uint256 = W256.of_int (512 + 928).

op VK_LOOKUP_TABLE_0_X_SLOT : uint256 = W256.of_int (512 + 960).
op VK_LOOKUP_TABLE_0_Y_SLOT : uint256 = W256.of_int (512 + 992).
op VK_LOOKUP_TABLE_1_X_SLOT : uint256 = W256.of_int (512 + 1024).
op VK_LOOKUP_TABLE_1_Y_SLOT : uint256 = W256.of_int (512 + 1056).
op VK_LOOKUP_TABLE_2_X_SLOT : uint256 = W256.of_int (512 + 1088).
op VK_LOOKUP_TABLE_2_Y_SLOT : uint256 = W256.of_int (512 + 1120).
op VK_LOOKUP_TABLE_3_X_SLOT : uint256 = W256.of_int (512 + 1152).
op VK_LOOKUP_TABLE_3_Y_SLOT : uint256 = W256.of_int (512 + 1184).

op VK_LOOKUP_TABLE_TYPE_X_SLOT : uint256 = W256.of_int (512 + 1216).
op VK_LOOKUP_TABLE_TYPE_Y_SLOT : uint256 = W256.of_int (512 + 1248).

op VK_RECURSIVE_FLAG_SLOT : uint256 = W256.of_int (512 + 1280).

(*    /*//////////////////////////////////////////////////////////////
                             Proof
    //////////////////////////////////////////////////////////////*/ *)

op PROOF_PUBLIC_INPUT : uint256 = W256.of_int (512 + 1312 + 0).

op PROOF_STATE_POLYS_0_X_SLOT : uint256 = W256.of_int (512 + 1312 + 32).
op PROOF_STATE_POLYS_0_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 64).
op PROOF_STATE_POLYS_1_X_SLOT : uint256 = W256.of_int (512 + 1312 + 96).
op PROOF_STATE_POLYS_1_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 128).
op PROOF_STATE_POLYS_2_X_SLOT : uint256 = W256.of_int (512 + 1312 + 160).
op PROOF_STATE_POLYS_2_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 192).
op PROOF_STATE_POLYS_3_X_SLOT : uint256 = W256.of_int (512 + 1312 + 224).
op PROOF_STATE_POLYS_3_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 256).

op PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT : uint256 = W256.of_int (512 + 1312 + 288).
op PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 320).

op PROOF_LOOKUP_S_POLY_X_SLOT : uint256 = W256.of_int (512 + 1312 + 352).
op PROOF_LOOKUP_S_POLY_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 384).

op PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT : uint256 = W256.of_int (512 + 1312 + 416).
op PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 448).

op PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT : uint256 = W256.of_int (512 + 1312 + 480).
op PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 512).
op PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT : uint256 = W256.of_int (512 + 1312 + 544).
op PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 576).
op PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT : uint256 = W256.of_int (512 + 1312 + 608).
op PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 640).
op PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT : uint256 = W256.of_int (512 + 1312 + 672).
op PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 704).

op PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 736).
op PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 768).
op PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 800).
op PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 832).

op PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT : uint256 = W256.of_int (512 + 1312 + 864).
op PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 896).

op PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 928).
op PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 960).
op PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 992).

op PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT : uint256 = W256.of_int (512 + 1312 + 1024).
op PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT : uint256 = W256.of_int (512 + 1312 + 1056).
op PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT : uint256 = W256.of_int (512 + 1312 + 1088).
op PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 1120).
op PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT : uint256 = W256.of_int (512 + 1312 + 1152).
op PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 1184).
op PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 1216).
op PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 1248).
op PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 1280).

op PROOF_OPENING_PROOF_AT_Z_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1312).
op PROOF_OPENING_PROOF_AT_Z_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1344).
op PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1376).
op PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1408).

op PROOF_RECURSIVE_PART_P1_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1440).
op PROOF_RECURSIVE_PART_P1_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1472).

op PROOF_RECURSIVE_PART_P2_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1504).
op PROOF_RECURSIVE_PART_P2_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1536).

(*    /*//////////////////////////////////////////////////////////////
                             Transcript slot
    //////////////////////////////////////////////////////////////*/ *)

op TRANSCRIPT_BEGIN_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 0).
op TRANSCRIPT_DST_BYTE_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 3).
op TRANSCRIPT_STATE_0_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 4).
op TRANSCRIPT_STATE_1_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 36).
op TRANSCRIPT_CHALLENGE_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 68).

(*    /*//////////////////////////////////////////////////////////////
                             Partial verifier state
    //////////////////////////////////////////////////////////////*/ *)

op STATE_ALPHA_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 0).
op STATE_BETA_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 32).
op STATE_GAMMA_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 64).
op STATE_POWER_OF_ALPHA_2_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 96).
op STATE_POWER_OF_ALPHA_3_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 128).
op STATE_POWER_OF_ALPHA_4_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 160).
op STATE_POWER_OF_ALPHA_5_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 192).
op STATE_POWER_OF_ALPHA_6_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 224).
op STATE_POWER_OF_ALPHA_7_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 256).
op STATE_POWER_OF_ALPHA_8_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 288).
op STATE_ETA_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 320).
op STATE_BETA_LOOKUP_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 352).
op STATE_GAMMA_LOOKUP_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 384).
op STATE_BETA_PLUS_ONE_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 416).
op STATE_BETA_GAMMA_PLUS_GAMMA_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 448).
op STATE_V_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 480).
op STATE_U_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 512).
op STATE_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 544).
op STATE_Z_MINUS_LAST_OMEGA_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 576).
op STATE_L_0_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 608).
op STATE_L_N_MINUS_ONE_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 640).
op STATE_Z_IN_DOMAIN_SIZE : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 672).

(*    /*//////////////////////////////////////////////////////////////
                             Queries
    //////////////////////////////////////////////////////////////*/ *)

op QUERIES_BUFFER_POINT_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 0).

op QUERIES_AT_Z_0_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 64).
op QUERIES_AT_Z_0_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 96).
op QUERIES_AT_Z_1_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 128).
op QUERIES_AT_Z_1_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 160).

op QUERIES_T_POLY_AGGREGATED_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 192).
op QUERIES_T_POLY_AGGREGATED_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 224).

(*    /*//////////////////////////////////////////////////////////////
                             Aggregated commitment
    //////////////////////////////////////////////////////////////*/ *)

op AGGREGATED_AT_Z_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 256 + 0).
op AGGREGATED_AT_Z_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 256 + 32).

op AGGREGATED_AT_Z_OMEGA_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 256 + 64).
op AGGREGATED_AT_Z_OMEGA_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 256 + 96).

op AGGREGATED_OPENING_AT_Z_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 256 + 128).
op AGGREGATED_OPENING_AT_Z_OMEGA_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 256 + 160).

(*    /*//////////////////////////////////////////////////////////////
                             Pairing data
    //////////////////////////////////////////////////////////////*/ *)

op PAIRING_BUFFER_POINT_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 256 + 192 + 0).
op PAIRING_BUFFER_POINT_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 256 + 192 + 32).

op PAIRING_PAIR_WITH_GENERATOR_X_SLOT =
        512 + 1312 + 1568 + 128 + 704 + 256 + 192 + 64.
op PAIRING_PAIR_WITH_GENERATOR_Y_SLOT =
        512 + 1312 + 1568 + 128 + 704 + 256 + 192 + 96.

op PAIRING_PAIR_WITH_X_X_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 256 + 256 + 128).
op PAIRING_PAIR_WITH_X_Y_SLOT : uint256 = W256.of_int (512 + 1312 + 1568 + 128 + 704 + 256 + 256 + 160).

(*    /*//////////////////////////////////////////////////////////////
               Slots for scalar multiplication optimizations
    //////////////////////////////////////////////////////////////*/ *)

op COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF =
        512 + 1312 + 1568 + 128 + 704 + 256 + 256 + 192.
op LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF =
        512 + 1312 + 1568 + 128 + 704 + 256 + 256 + 224.
op LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF =
        512 + 1312 + 1568 + 128 + 704 + 256 + 256 + 256.

(*    /*//////////////////////////////////////////////////////////////
                             Constants
    //////////////////////////////////////////////////////////////*/ *)

op OMEGA : uint256 = W256.of_int 13446667982376394161563610564587413125564757801019538732601045199901075958935.
op DOMAIN_SIZE : uint256 = W256.of_int 67108864. (* // 2^26 *)
op Q_MOD : uint256 = W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583.
op R_MOD : uint256 = W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617.

(*    /// @dev flip of 0xe000000000000000000000000000000000000000000000000000000000000000). *)
op FR_MASK : uint256 = W256.of_int 14474011154664524427946373126085988481658748083205070504932198000989141204991.

(*    // non residues *)
op NON_RESIDUES_0 : uint256 = W256.of_int 5.
op NON_RESIDUES_1 : uint256 = W256.of_int 7.
op NON_RESIDUES_2 : uint256 = W256.of_int 10.

(*    // trusted setup g2 elements *)
op G2_ELEMENTS_0_X1 : uint256 = W256.of_int 11559732032986387107991004021392285783925812861821192530917403151452391805634.
op G2_ELEMENTS_0_X2 : uint256 = W256.of_int 10857046999023057135944570762232829481370756359578518086990519993285655852781.
op G2_ELEMENTS_0_Y1 : uint256 = W256.of_int 4082367875863433681332203403145435568316851327593401208105741076214120093531.
op G2_ELEMENTS_0_Y2 : uint256 = W256.of_int 8495653923123431417604973247489272438418190587263600148770280649306958101930.
op G2_ELEMENTS_1_X1 : uint256 = W256.of_int 17212635814319756364507010169094758005397460366678210664966334781961899574209.
op G2_ELEMENTS_1_X2 : uint256 = W256.of_int 496075682290949347282619629729389528669750910289829251317610107342504362928.
op G2_ELEMENTS_1_Y1 : uint256 = W256.of_int 2255182984359105691812395885056400739448730162863181907784180250290003009508.
op G2_ELEMENTS_1_Y2 : uint256 = W256.of_int 15828724851114720558251891430452666121603726704878231219287131634746610441813.
