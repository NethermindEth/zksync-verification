require import UInt256 PurePrimops YulPrimops YulTests.

(* Begin Verifier_1261 *)
op cleanup_bytes32(value : uint256): uint256 = value.

op zero_value_for_split_bool: uint256 = (W256.of_int 0).

op zero_value_for_split_bytes32: uint256 = (W256.of_int 0).

op STRING : int = 0.

module Verifier = {
  proc usr_revertWithMessage(usr_len : uint256, usr_reason : uint256): unit = {
    var _1, _2, _3, _4, _5, _6, _7;
    _1 <- (PurePrimops.shl (W256.of_int 229) (W256.of_int 4594637));
    _2 <- (W256.of_int 0);
    Primops.mstore(_2, _1);
    _3 <- (W256.of_int 32);
    _4 <- (W256.of_int 4);
    Primops.mstore(_4, _3);
    _5 <- (W256.of_int 36);
    Primops.mstore(_5, usr_len);
    _6 <- (W256.of_int 68);
    Primops.mstore(_6, usr_reason);
    _7 <- (W256.of_int 100);
    Primops.revert(_2, _7);
    }
  
  proc revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  proc revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  proc revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  proc usr_getTranscriptChallenge(usr_numberOfChallenge : uint256): uint256 = {
    var usr_challenge, _1, _2, _3, _4, _5, _6, _7, _8, _9, tmp94;
    _1 <- (W256.of_int 2);
    _2 <- (W256.of_int 3395);
    Primops.mstore8(_2, _1);
    _3 <- (W256.of_int 224);
    _4 <- (PurePrimops.shl _3 usr_numberOfChallenge);
    _5 <- (W256.of_int 3460);
    Primops.mstore(_5, _4);
    _6 <- ((PurePrimops.shl (W256.of_int 253) (W256.of_int 1)) - (W256.of_int 1));
    _7 <- (W256.of_int 72);
    _8 <- (W256.of_int 3392);
    tmp94 <@ Primops.keccak256(_8, _7);
    _9 <- tmp94;
    usr_challenge <- (PurePrimops.bit_and _9 _6);
    return usr_challenge;
    }
  
  proc allocate_unbounded(): uint256 = {
    var memPtr, _1, tmp16;
    _1 <- (W256.of_int 64);
    tmp16 <@ Primops.mload(_1);
    memPtr <- tmp16;
    return memPtr;
    }
  
  proc usr_permutationQuotientContribution(): uint256 = {
    var usr_res, _1, _2, _3, tmp270, _4, _5, tmp271, _6, usr_gamma, tmp272, _7, usr_beta, tmp273, usr_factorMultiplier, _8, _9, tmp274, _10, _11, tmp275, _12, _13, tmp276, _14, _15, tmp277, _16, _17, tmp278, _18, _19, tmp279, _20, _21, tmp280, _22, _23, usr_l0AtZ, tmp281, _24, _25, tmp282, _26;
    _1 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _2 <- (W256.of_int 2848);
    tmp270 <@ Primops.mload(_2);
    _3 <- tmp270;
    _4 <- (W256.of_int 3680);
    tmp271 <@ Primops.mload(_4);
    _5 <- tmp271;
    usr_res <- (PurePrimops.mulmod _5 _3 _1);
    _6 <- (W256.of_int 3584);
    tmp272 <@ Primops.mload(_6);
    usr_gamma <- tmp272;
    _7 <- (W256.of_int 3552);
    tmp273 <@ Primops.mload(_7);
    usr_beta <- tmp273;
    _8 <- (W256.of_int 2752);
    tmp274 <@ Primops.mload(_8);
    _9 <- tmp274;
    usr_factorMultiplier <- (PurePrimops.mulmod _9 usr_beta _1);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma _1);
    _10 <- (W256.of_int 2560);
    tmp275 <@ Primops.mload(_10);
    _11 <- tmp275;
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier _11 _1);
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier _1);
    _12 <- (W256.of_int 2784);
    tmp276 <@ Primops.mload(_12);
    _13 <- tmp276;
    usr_factorMultiplier <- (PurePrimops.mulmod _13 usr_beta _1);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma _1);
    _14 <- (W256.of_int 2592);
    tmp277 <@ Primops.mload(_14);
    _15 <- tmp277;
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier _15 _1);
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier _1);
    _16 <- (W256.of_int 2816);
    tmp278 <@ Primops.mload(_16);
    _17 <- tmp278;
    usr_factorMultiplier <- (PurePrimops.mulmod _17 usr_beta _1);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma _1);
    _18 <- (W256.of_int 2624);
    tmp279 <@ Primops.mload(_18);
    _19 <- tmp279;
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier _19 _1);
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier _1);
    _20 <- (W256.of_int 2656);
    tmp280 <@ Primops.mload(_20);
    _21 <- tmp280;
    _22 <- (PurePrimops.addmod _21 usr_gamma _1);
    usr_res <- (PurePrimops.mulmod usr_res _22 _1);
    usr_res <- (_1 - usr_res);
    _23 <- (W256.of_int 4128);
    tmp281 <@ Primops.mload(_23);
    usr_l0AtZ <- tmp281;
    _24 <- (W256.of_int 3712);
    tmp282 <@ Primops.mload(_24);
    _25 <- tmp282;
    usr_l0AtZ <- (PurePrimops.mulmod usr_l0AtZ _25 _1);
    _26 <- (_1 - usr_l0AtZ);
    usr_res <- (PurePrimops.addmod usr_res _26 _1);
    return usr_res;
    }
  
  proc constructor_IVerifier(): unit = {
    }
  
  proc usr_addAssignLookupLinearisationContributionWithV(usr_dest : uint256, usr_stateOpening0AtZ : uint256, usr_stateOpening1AtZ : uint256, usr_stateOpening2AtZ : uint256): unit = {
    var _1, usr_factor, tmp330, _2, tmp331, _3, tmp332, _4, _5, tmp333, _6, _7, tmp334, _8, _9, tmp335, _10, _11, tmp336, _12, _13, tmp337, usr_fReconstructed, _14, usr_eta, tmp338, usr_currentEta, _15, _16, _17, _18, tmp339, _19, _20, _21, tmp340, _22, _23, tmp341, _24, _25, tmp342, _26, tmp343, _27, tmp344, _28, _29, tmp345, _30, _31, tmp346, _32, _33, _34, tmp347, _35, _36, tmp348, _37, _38, tmp349, _39;
    _1 <- (W256.of_int 2912);
    tmp330 <@ Primops.mload(_1);
    usr_factor <- tmp330;
    tmp331 <@ Primops.mload((W256.of_int 3744));
    _2 <- tmp331;
    usr_factor <- (PurePrimops.mulmod usr_factor _2 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    tmp332 <@ Primops.mload((W256.of_int 4096));
    _3 <- tmp332;
    usr_factor <- (PurePrimops.mulmod usr_factor _3 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _4 <- (W256.of_int 4000);
    tmp333 <@ Primops.mload(_4);
    _5 <- tmp333;
    usr_factor <- (PurePrimops.mulmod usr_factor _5 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _6 <- (W256.of_int 4992);
    Primops.mstore(_6, usr_factor);
    _7 <- (W256.of_int 2976);
    tmp334 <@ Primops.mload(_7);
    usr_factor <- tmp334;
    _8 <- (W256.of_int 3872);
    tmp335 <@ Primops.mload(_8);
    _9 <- tmp335;
    usr_factor <- (PurePrimops.mulmod usr_factor _9 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _10 <- (W256.of_int 2944);
    tmp336 <@ Primops.mload(_10);
    _11 <- tmp336;
    usr_factor <- (PurePrimops.addmod usr_factor _11 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _12 <- (W256.of_int 3968);
    tmp337 <@ Primops.mload(_12);
    _13 <- tmp337;
    usr_factor <- (PurePrimops.addmod usr_factor _13 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_fReconstructed <- usr_stateOpening0AtZ;
    _14 <- (W256.of_int 3840);
    tmp338 <@ Primops.mload(_14);
    usr_eta <- tmp338;
    usr_currentEta <- usr_eta;
    _15 <- (PurePrimops.mulmod usr_eta usr_stateOpening1AtZ (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_fReconstructed <- (PurePrimops.addmod usr_stateOpening0AtZ _15 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_currentEta <- (PurePrimops.mulmod usr_eta usr_eta (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _16 <- (PurePrimops.mulmod usr_currentEta usr_stateOpening2AtZ (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_fReconstructed <- (PurePrimops.addmod usr_fReconstructed _16 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_currentEta <- (PurePrimops.mulmod usr_currentEta usr_eta (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _17 <- (W256.of_int 3040);
    tmp339 <@ Primops.mload(_17);
    _18 <- tmp339;
    _19 <- (PurePrimops.mulmod _18 usr_currentEta (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_fReconstructed <- (PurePrimops.addmod usr_fReconstructed _19 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _20 <- (W256.of_int 3008);
    tmp340 <@ Primops.mload(_20);
    _21 <- tmp340;
    usr_fReconstructed <- (PurePrimops.mulmod usr_fReconstructed _21 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _22 <- (W256.of_int 3904);
    tmp341 <@ Primops.mload(_22);
    _23 <- tmp341;
    usr_fReconstructed <- (PurePrimops.addmod usr_fReconstructed _23 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.mulmod usr_factor usr_fReconstructed (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _24 <- (W256.of_int 3936);
    tmp342 <@ Primops.mload(_24);
    _25 <- tmp342;
    usr_factor <- (PurePrimops.mulmod usr_factor _25 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- ((W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617) - usr_factor);
    tmp343 <@ Primops.mload((W256.of_int 3744));
    _26 <- tmp343;
    usr_factor <- (PurePrimops.mulmod usr_factor _26 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    tmp344 <@ Primops.mload((W256.of_int 4096));
    _27 <- tmp344;
    usr_factor <- (PurePrimops.mulmod usr_factor _27 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _28 <- (W256.of_int 3776);
    tmp345 <@ Primops.mload(_28);
    _29 <- tmp345;
    _30 <- (W256.of_int 4128);
    tmp346 <@ Primops.mload(_30);
    _31 <- tmp346;
    _32 <- (PurePrimops.mulmod _31 _29 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.addmod usr_factor _32 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _33 <- (W256.of_int 3808);
    tmp347 <@ Primops.mload(_33);
    _34 <- tmp347;
    _35 <- (W256.of_int 4160);
    tmp348 <@ Primops.mload(_35);
    _36 <- tmp348;
    _37 <- (PurePrimops.mulmod _36 _34 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.addmod usr_factor _37 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    tmp349 <@ Primops.mload(_4);
    _38 <- tmp349;
    usr_factor <- (PurePrimops.mulmod usr_factor _38 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _39 <- (W256.of_int 4960);
    Primops.mstore(_39, usr_factor);
    }
  
  proc revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  proc cleanup_bool(value : uint256): uint256 = {
    var cleaned, _1;
    _1 <- (PurePrimops.iszero value);
    cleaned <- (PurePrimops.iszero _1);
    return cleaned;
    }
  
  proc revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  proc revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  proc fun_loadVerificationKey(): unit = {
    var _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21, _22, _23, _24, _25, _26, _27, _28, _29, _30, _31, _32, _33, _34, _35, _36, _37, _38, _39, _40, _41, _42, _43, _44, _45, _46, _47, _48, _49, _50, _51, _52, _53, _54, _55, _56, _57, _58, _59, _60, _61, _62, _63, _64, _65, _66, _67, _68, _69, _70, _71, _72, _73, _74, _75, _76, _77, _78, _79, _80, _81, _82;
    _1 <- (W256.of_int 8752182643819278825281358491109311747488397345835400146720638359015287854690);
    _2 <- (W256.of_int 512);
    Primops.mstore(_2, _1);
    _3 <- (W256.of_int 11702890106774794311109464320829961639285524182517416836480964755620593036625);
    _4 <- (W256.of_int 544);
    Primops.mstore(_4, _3);
    _5 <- (W256.of_int 20333726085237242816528533108173405517277666887513325731527458638169740323846);
    _6 <- (W256.of_int 576);
    Primops.mstore(_6, _5);
    _7 <- (W256.of_int 20895759739260899082484353863151962651671811489085862903974918191239970565727);
    _8 <- (W256.of_int 608);
    Primops.mstore(_8, _7);
    _9 <- (W256.of_int 1568732599965362807326380099663611053862348508639087822144187543479274466412);
    _10 <- (W256.of_int 640);
    Primops.mstore(_10, _9);
    _11 <- (W256.of_int 5821054758250780059685638301776364871013117602597489359484409980131967326794);
    _12 <- (W256.of_int 672);
    Primops.mstore(_12, _11);
    _13 <- (W256.of_int 1869564366554527726271945732583360837778279311090061338642468249261166609475);
    _14 <- (W256.of_int 704);
    Primops.mstore(_14, _13);
    _15 <- (W256.of_int 6787073056745945161826226704190290609825180409911049644428579916838155209697);
    _16 <- (W256.of_int 736);
    Primops.mstore(_16, _15);
    _17 <- (W256.of_int 457576930265342335264945522969406804501107665328727087867171094316559181535);
    _18 <- (W256.of_int 768);
    Primops.mstore(_18, _17);
    _19 <- (W256.of_int 15424863073888926344027107060444259361026863904290125685775015743583967752523);
    _20 <- (W256.of_int 800);
    Primops.mstore(_20, _19);
    _21 <- (W256.of_int 17470132079837949645292768946901897910488674334073656384858846314172720305794);
    _22 <- (W256.of_int 832);
    Primops.mstore(_22, _21);
    _23 <- (W256.of_int 545412623592733862227844066395948813122937527333953380716629283051527996076);
    _24 <- (W256.of_int 864);
    Primops.mstore(_24, _23);
    _25 <- (W256.of_int 3542620684081214281078362979824071457719243923292217179618867142734017714197);
    _26 <- (W256.of_int 896);
    Primops.mstore(_26, _25);
    _27 <- (W256.of_int 10380438707000372753007289103897630883671902212004026295360039945231108187502);
    _28 <- (W256.of_int 928);
    Primops.mstore(_28, _27);
    _29 <- (W256.of_int 13086775255118926036233880981068687796723800497694631087151014741591951564618);
    _30 <- (W256.of_int 960);
    Primops.mstore(_30, _29);
    _31 <- (W256.of_int 97194583370920108185062801930585216368005987855712538133473341181290744675);
    _32 <- (W256.of_int 992);
    Primops.mstore(_32, _31);
    _33 <- (W256.of_int 11090534100914016361232447120294745393211436081860550365760620284449885924457);
    _34 <- (W256.of_int 1024);
    Primops.mstore(_34, _33);
    _35 <- (W256.of_int 6190121082107679677011313308624936965782748053078710395209485205617091614781);
    _36 <- (W256.of_int 1056);
    Primops.mstore(_36, _35);
    _37 <- (W256.of_int 15086136319636422536776088427553286399949509263897119922379735045147898875009);
    _38 <- (W256.of_int 1088);
    Primops.mstore(_38, _37);
    _39 <- (W256.of_int 14330561162787072568797012175184761164763459595199124517037991495673925464785);
    _40 <- (W256.of_int 1120);
    Primops.mstore(_40, _39);
    _41 <- (W256.of_int 21323538885080684424185174689480993185750201390966223018512354418490677522148);
    _42 <- (W256.of_int 1152);
    Primops.mstore(_42, _41);
    _43 <- (W256.of_int 13825385863192118646834397710139923872086647553258488355179808994788744210563);
    _44 <- (W256.of_int 1184);
    Primops.mstore(_44, _43);
    _45 <- (W256.of_int 8390759602848414205412884900126185284679301543388803089358900543850868129488);
    _46 <- (W256.of_int 1216);
    Primops.mstore(_46, _45);
    _47 <- (W256.of_int 7069161667387011886642940009688789554068768218554020114127791736575843662652);
    _48 <- (W256.of_int 1248);
    Primops.mstore(_48, _47);
    _49 <- (W256.of_int 21779692208264067614279093821878517213862501879831804234566704419708093761485);
    _50 <- (W256.of_int 1280);
    Primops.mstore(_50, _49);
    _51 <- (W256.of_int 14513193766097634962386283396255157053671281137962954471134782133605379519908);
    _52 <- (W256.of_int 1312);
    Primops.mstore(_52, _51);
    _53 <- (W256.of_int 4751267043421347170875860608378639586591867931662910797110300384786346064625);
    _54 <- (W256.of_int 1344);
    Primops.mstore(_54, _53);
    _55 <- (W256.of_int 11385717438670984215358012358002661303410243223751533068904005282628107986385);
    _56 <- (W256.of_int 1376);
    Primops.mstore(_56, _55);
    _57 <- (W256.of_int 20045313662746578028950791395157660351198208045597010788369662325700141348443);
    _58 <- (W256.of_int 1472);
    Primops.mstore(_58, _57);
    _59 <- (W256.of_int 2200761695078532224145807378118591946349840073460005094399078719163643466856);
    _60 <- (W256.of_int 1504);
    Primops.mstore(_60, _59);
    _61 <- (W256.of_int 13866646217607640441607041956684111087071997201218815349460750486791109380780);
    _62 <- (W256.of_int 1536);
    Primops.mstore(_62, _61);
    _63 <- (W256.of_int 13178446611795019678701878053235714968797421377761816259103804833273256298333);
    _64 <- (W256.of_int 1568);
    Primops.mstore(_64, _63);
    _65 <- (W256.of_int 5057503605752869531452842486824745179648819794307492731589448195268672785801);
    _66 <- (W256.of_int 1600);
    Primops.mstore(_66, _65);
    _67 <- (W256.of_int 8597434312520299647191152876265164941580478223412397470356037586993894367875);
    _68 <- (W256.of_int 1632);
    Primops.mstore(_68, _67);
    _69 <- (W256.of_int 1342318055425277544055386589364579054544440640110901993487861472578322387903);
    _70 <- (W256.of_int 1664);
    Primops.mstore(_70, _69);
    _71 <- (W256.of_int 4438354282468267034382897187461199764068502038746983055473062465446039509158);
    _72 <- (W256.of_int 1696);
    Primops.mstore(_72, _71);
    _73 <- (W256.of_int 21714794642552531775933093644480516421064284615960245486122726724547638127878);
    _74 <- (W256.of_int 1408);
    Primops.mstore(_74, _73);
    _75 <- (W256.of_int 20374981665942106195451736226451722737514281476778224282304648903722926579601);
    _76 <- (W256.of_int 1440);
    Primops.mstore(_76, _75);
    _77 <- (W256.of_int 196778531949039689886328474582670216324308721975620885373710029662715787742);
    _78 <- (W256.of_int 1728);
    Primops.mstore(_78, _77);
    _79 <- (W256.of_int 11005776646725047106517461026899305486268481542412200771754169232553006481646);
    _80 <- (W256.of_int 1760);
    Primops.mstore(_80, _79);
    _81 <- (W256.of_int 0);
    _82 <- (W256.of_int 1792);
    Primops.mstore(_82, _81);
    }
  
  proc revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  proc usr_updateTranscript(usr_value : uint256): unit = {
    var _1, _2, _3, _4, _5, usr_newState0, tmp92, _6, usr_newState1, tmp93, _7, _8;
    _1 <- (W256.of_int 0);
    _2 <- (W256.of_int 3395);
    Primops.mstore8(_2, _1);
    _3 <- (W256.of_int 3460);
    Primops.mstore(_3, usr_value);
    _4 <- (W256.of_int 100);
    _5 <- (W256.of_int 3392);
    tmp92 <@ Primops.keccak256(_5, _4);
    usr_newState0 <- tmp92;
    _6 <- (W256.of_int 1);
    Primops.mstore8(_2, _6);
    tmp93 <@ Primops.keccak256(_5, _4);
    usr_newState1 <- tmp93;
    _7 <- (W256.of_int 3428);
    Primops.mstore(_7, usr_newState1);
    _8 <- (W256.of_int 3396);
    Primops.mstore(_8, usr_newState0);
    }
  
  proc shift_right_unsigned(value : uint256): uint256 = {
    var newValue, _1;
    _1 <- (W256.of_int 224);
    newValue <- (PurePrimops.shr _1 value);
    return newValue;
    }
  
  proc usr_pointAddAssign(usr_p1 : uint256, usr_p2 : uint256): unit = {
    var _1, tmp72, _2, _3, _4, _5, tmp73, _6, tmp74, _7, _8, _9, tmp75, _10, _11, _12, _13, tmp76, _14, tmp77, _15, _16, _17, tmp78;
    tmp72 <@ Primops.mload(usr_p1);
    _1 <- tmp72;
    _2 <- (W256.of_int 0);
    Primops.mstore(_2, _1);
    _3 <- (W256.of_int 32);
    _4 <- (usr_p1 + _3);
    tmp73 <@ Primops.mload(_4);
    _5 <- tmp73;
    Primops.mstore(_3, _5);
    tmp74 <@ Primops.mload(usr_p2);
    _6 <- tmp74;
    _7 <- (W256.of_int 64);
    Primops.mstore(_7, _6);
    _8 <- (usr_p2 + _3);
    tmp75 <@ Primops.mload(_8);
    _9 <- tmp75;
    _10 <- (W256.of_int 96);
    Primops.mstore(_10, _9);
    _11 <- (W256.of_int 128);
    _12 <- (W256.of_int 6);
    tmp76 <@ Primops.gas();
    _13 <- tmp76;
    tmp77 <@ Primops.staticcall(_13, _12, _2, _11, usr_p1, _7);
    _14 <- tmp77;
    _15 <- (PurePrimops.iszero _14);
    if ((bool_of_uint256 _15))
      {
      _16 <- (W256.of_int STRING (*pointAddAssign: ecAdd failed*));
      _17 <- (W256.of_int 28);
      tmp78 <@ usr_revertWithMessage(_17, _16);
      
      }
    
    }
  
  proc usr_pointMulIntoDest(usr_point : uint256, usr_s : uint256, usr_dest : uint256): unit = {
    var _1, tmp53, _2, _3, _4, _5, tmp54, _6, _7, _8, _9, tmp55, _10, tmp56, _11, _12, _13, tmp57;
    tmp53 <@ Primops.mload(usr_point);
    _1 <- tmp53;
    _2 <- (W256.of_int 0);
    Primops.mstore(_2, _1);
    _3 <- (W256.of_int 32);
    _4 <- (usr_point + _3);
    tmp54 <@ Primops.mload(_4);
    _5 <- tmp54;
    Primops.mstore(_3, _5);
    _6 <- (W256.of_int 64);
    Primops.mstore(_6, usr_s);
    _7 <- (W256.of_int 96);
    _8 <- (W256.of_int 7);
    tmp55 <@ Primops.gas();
    _9 <- tmp55;
    tmp56 <@ Primops.staticcall(_9, _8, _2, _7, usr_dest, _6);
    _10 <- tmp56;
    _11 <- (PurePrimops.iszero _10);
    if ((bool_of_uint256 _11))
      {
      _12 <- (W256.of_int STRING (*pointMulIntoDest: ecMul failed*));
      _13 <- (W256.of_int 30);
      tmp57 <@ usr_revertWithMessage(_13, _12);
      
      }
    
    }
  
  proc usr_loadProof(): unit = {
    var _1, usr_offset, tmp95, _2, usr_publicInputLengthInWords, tmp96, _3, usr_isValid, _4, _5, _6, _7, tmp97, _8, _9, tmp98, _10, usr_proofLengthInWords, tmp99, _11, _12, _13, _14, _15, tmp100, usr_x, _16, _17, _18, tmp101, usr_y, usr_xx, _19, _20, _21, _22, _23, _24, _25, _26, _27, _28, tmp102, usr_x_1, _29, _30, _31, tmp103, usr_y_1, usr_xx_1, _32, _33, _34, _35, _36, _37, _38, _39, _40, tmp104, usr_x_2, _41, _42, _43, tmp105, usr_y_2, usr_xx_2, _44, _45, _46, _47, _48, _49, _50, _51, _52, tmp106, usr_x_3, _53, _54, _55, tmp107, usr_y_3, usr_xx_3, _56, _57, _58, _59, _60, _61, _62, _63, _64, tmp108, usr_x_4, _65, _66, _67, tmp109, usr_y_4, usr_xx_4, _68, _69, _70, _71, _72, _73, _74, _75, _76, tmp110, usr_x_5, _77, _78, _79, tmp111, usr_y_5, usr_xx_5, _80, _81, _82, _83, _84, _85, _86, _87, _88, tmp112, usr_x_6, _89, _90, _91, tmp113, usr_y_6, usr_xx_6, _92, _93, _94, _95, _96, _97, _98, _99, _100, tmp114, usr_x_7, _101, _102, _103, tmp115, usr_y_7, usr_xx_7, _104, _105, _106, _107, _108, _109, _110, _111, _112, tmp116, usr_x_8, _113, _114, _115, tmp117, usr_y_8, usr_xx_8, _116, _117, _118, _119, _120, _121, _122, _123, _124, tmp118, usr_x_9, _125, _126, _127, tmp119, usr_y_9, usr_xx_9, _128, _129, _130, _131, _132, _133, _134, _135, _136, tmp120, usr_x_10, _137, _138, _139, tmp121, usr_y_10, usr_xx_10, _140, _141, _142, _143, _144, _145, _146, _147, _148, _149, tmp122, _150, _151, _152, _153, _154, tmp123, _155, _156, _157, _158, _159, tmp124, _160, _161, _162, _163, _164, tmp125, _165, _166, _167, _168, _169, tmp126, _170, _171, _172, _173, _174, tmp127, _175, _176, _177, _178, _179, tmp128, _180, _181, _182, _183, _184, tmp129, _185, _186, _187, _188, _189, tmp130, _190, _191, _192, _193, _194, tmp131, _195, _196, _197, _198, _199, tmp132, _200, _201, _202, _203, _204, tmp133, _205, _206, _207, _208, _209, tmp134, _210, _211, _212, _213, _214, tmp135, _215, _216, _217, _218, _219, tmp136, _220, _221, _222, _223, _224, tmp137, _225, _226, _227, _228, _229, tmp138, _230, _231, _232, _233, _234, tmp139, _235, _236, _237, _238, _239, tmp140, usr_x_11, _240, _241, _242, tmp141, usr_y_11, usr_xx_11, _243, _244, _245, _246, _247, _248, _249, _250, _251, tmp142, usr_x_12, _252, _253, _254, tmp143, usr_y_12, usr_xx_12, _255, _256, _257, _258, _259, _260, tmp144, _261, usr_recursiveProofLengthInWords, tmp145, _262, _263, tmp146, tmp147, _264, _265, _266, _267, tmp148, usr_x_13, _268, _269, tmp149, usr_y_13, usr_xx_13, _270, _271, _272, _273, _274, _275, _276, _277, tmp150, usr_x_14, _278, _279, tmp151, usr_y_14, usr_xx_14, _280, _281, _282, _283, _284, _285, _286, _287, _288, tmp152;
    _1 <- (W256.of_int 4);
    tmp95 <@ Primops.calldataload(_1);
    usr_offset <- tmp95;
    _2 <- (usr_offset + _1);
    tmp96 <@ Primops.calldataload(_2);
    usr_publicInputLengthInWords <- tmp96;
    _3 <- (W256.of_int 1);
    usr_isValid <- (PurePrimops.eq_uint256 usr_publicInputLengthInWords _3);
    _4 <- ((PurePrimops.shl (W256.of_int 253) (W256.of_int 1)) - (W256.of_int 1));
    _5 <- (W256.of_int 36);
    _6 <- (usr_offset + _5);
    tmp97 <@ Primops.calldataload(_6);
    _7 <- tmp97;
    _8 <- (PurePrimops.bit_and _7 _4);
    _9 <- (W256.of_int 1824);
    Primops.mstore(_9, _8);
    tmp98 <@ Primops.calldataload(_5);
    usr_offset <- tmp98;
    _10 <- (usr_offset + _1);
    tmp99 <@ Primops.calldataload(_10);
    usr_proofLengthInWords <- tmp99;
    _11 <- (W256.of_int 44);
    _12 <- (PurePrimops.eq_uint256 usr_proofLengthInWords _11);
    usr_isValid <- (PurePrimops.bit_and _12 usr_isValid);
    _13 <- (W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583);
    _14 <- (usr_offset + _5);
    tmp100 <@ Primops.calldataload(_14);
    _15 <- tmp100;
    usr_x <- (_15 %% _13);
    _16 <- (W256.of_int 68);
    _17 <- (usr_offset + _16);
    tmp101 <@ Primops.calldataload(_17);
    _18 <- tmp101;
    usr_y <- (_18 %% _13);
    usr_xx <- (PurePrimops.mulmod usr_x usr_x _13);
    _19 <- (W256.of_int 3);
    _20 <- (PurePrimops.mulmod usr_x usr_xx _13);
    _21 <- (PurePrimops.addmod _20 _19 _13);
    _22 <- (PurePrimops.mulmod usr_y usr_y _13);
    _23 <- (PurePrimops.eq_uint256 _22 _21);
    usr_isValid <- (PurePrimops.bit_and _23 usr_isValid);
    _24 <- (W256.of_int 1856);
    Primops.mstore(_24, usr_x);
    _25 <- (W256.of_int 1888);
    Primops.mstore(_25, usr_y);
    _26 <- (W256.of_int 100);
    _27 <- (usr_offset + _26);
    tmp102 <@ Primops.calldataload(_27);
    _28 <- tmp102;
    usr_x_1 <- (_28 %% _13);
    _29 <- (W256.of_int 132);
    _30 <- (usr_offset + _29);
    tmp103 <@ Primops.calldataload(_30);
    _31 <- tmp103;
    usr_y_1 <- (_31 %% _13);
    usr_xx_1 <- (PurePrimops.mulmod usr_x_1 usr_x_1 _13);
    _32 <- (PurePrimops.mulmod usr_x_1 usr_xx_1 _13);
    _33 <- (PurePrimops.addmod _32 _19 _13);
    _34 <- (PurePrimops.mulmod usr_y_1 usr_y_1 _13);
    _35 <- (PurePrimops.eq_uint256 _34 _33);
    usr_isValid <- (PurePrimops.bit_and _35 usr_isValid);
    _36 <- (W256.of_int 1920);
    Primops.mstore(_36, usr_x_1);
    _37 <- (W256.of_int 1952);
    Primops.mstore(_37, usr_y_1);
    _38 <- (W256.of_int 164);
    _39 <- (usr_offset + _38);
    tmp104 <@ Primops.calldataload(_39);
    _40 <- tmp104;
    usr_x_2 <- (_40 %% _13);
    _41 <- (W256.of_int 196);
    _42 <- (usr_offset + _41);
    tmp105 <@ Primops.calldataload(_42);
    _43 <- tmp105;
    usr_y_2 <- (_43 %% _13);
    usr_xx_2 <- (PurePrimops.mulmod usr_x_2 usr_x_2 _13);
    _44 <- (PurePrimops.mulmod usr_x_2 usr_xx_2 _13);
    _45 <- (PurePrimops.addmod _44 _19 _13);
    _46 <- (PurePrimops.mulmod usr_y_2 usr_y_2 _13);
    _47 <- (PurePrimops.eq_uint256 _46 _45);
    usr_isValid <- (PurePrimops.bit_and _47 usr_isValid);
    _48 <- (W256.of_int 1984);
    Primops.mstore(_48, usr_x_2);
    _49 <- (W256.of_int 2016);
    Primops.mstore(_49, usr_y_2);
    _50 <- (W256.of_int 228);
    _51 <- (usr_offset + _50);
    tmp106 <@ Primops.calldataload(_51);
    _52 <- tmp106;
    usr_x_3 <- (_52 %% _13);
    _53 <- (W256.of_int 260);
    _54 <- (usr_offset + _53);
    tmp107 <@ Primops.calldataload(_54);
    _55 <- tmp107;
    usr_y_3 <- (_55 %% _13);
    usr_xx_3 <- (PurePrimops.mulmod usr_x_3 usr_x_3 _13);
    _56 <- (PurePrimops.mulmod usr_x_3 usr_xx_3 _13);
    _57 <- (PurePrimops.addmod _56 _19 _13);
    _58 <- (PurePrimops.mulmod usr_y_3 usr_y_3 _13);
    _59 <- (PurePrimops.eq_uint256 _58 _57);
    usr_isValid <- (PurePrimops.bit_and _59 usr_isValid);
    _60 <- (W256.of_int 2048);
    Primops.mstore(_60, usr_x_3);
    _61 <- (W256.of_int 2080);
    Primops.mstore(_61, usr_y_3);
    _62 <- (W256.of_int 292);
    _63 <- (usr_offset + _62);
    tmp108 <@ Primops.calldataload(_63);
    _64 <- tmp108;
    usr_x_4 <- (_64 %% _13);
    _65 <- (W256.of_int 324);
    _66 <- (usr_offset + _65);
    tmp109 <@ Primops.calldataload(_66);
    _67 <- tmp109;
    usr_y_4 <- (_67 %% _13);
    usr_xx_4 <- (PurePrimops.mulmod usr_x_4 usr_x_4 _13);
    _68 <- (PurePrimops.mulmod usr_x_4 usr_xx_4 _13);
    _69 <- (PurePrimops.addmod _68 _19 _13);
    _70 <- (PurePrimops.mulmod usr_y_4 usr_y_4 _13);
    _71 <- (PurePrimops.eq_uint256 _70 _69);
    usr_isValid <- (PurePrimops.bit_and _71 usr_isValid);
    _72 <- (W256.of_int 2112);
    Primops.mstore(_72, usr_x_4);
    _73 <- (W256.of_int 2144);
    Primops.mstore(_73, usr_y_4);
    _74 <- (W256.of_int 356);
    _75 <- (usr_offset + _74);
    tmp110 <@ Primops.calldataload(_75);
    _76 <- tmp110;
    usr_x_5 <- (_76 %% _13);
    _77 <- (W256.of_int 388);
    _78 <- (usr_offset + _77);
    tmp111 <@ Primops.calldataload(_78);
    _79 <- tmp111;
    usr_y_5 <- (_79 %% _13);
    usr_xx_5 <- (PurePrimops.mulmod usr_x_5 usr_x_5 _13);
    _80 <- (PurePrimops.mulmod usr_x_5 usr_xx_5 _13);
    _81 <- (PurePrimops.addmod _80 _19 _13);
    _82 <- (PurePrimops.mulmod usr_y_5 usr_y_5 _13);
    _83 <- (PurePrimops.eq_uint256 _82 _81);
    usr_isValid <- (PurePrimops.bit_and _83 usr_isValid);
    _84 <- (W256.of_int 2176);
    Primops.mstore(_84, usr_x_5);
    _85 <- (W256.of_int 2208);
    Primops.mstore(_85, usr_y_5);
    _86 <- (W256.of_int 420);
    _87 <- (usr_offset + _86);
    tmp112 <@ Primops.calldataload(_87);
    _88 <- tmp112;
    usr_x_6 <- (_88 %% _13);
    _89 <- (W256.of_int 452);
    _90 <- (usr_offset + _89);
    tmp113 <@ Primops.calldataload(_90);
    _91 <- tmp113;
    usr_y_6 <- (_91 %% _13);
    usr_xx_6 <- (PurePrimops.mulmod usr_x_6 usr_x_6 _13);
    _92 <- (PurePrimops.mulmod usr_x_6 usr_xx_6 _13);
    _93 <- (PurePrimops.addmod _92 _19 _13);
    _94 <- (PurePrimops.mulmod usr_y_6 usr_y_6 _13);
    _95 <- (PurePrimops.eq_uint256 _94 _93);
    usr_isValid <- (PurePrimops.bit_and _95 usr_isValid);
    _96 <- (W256.of_int 2240);
    Primops.mstore(_96, usr_x_6);
    _97 <- (W256.of_int 2272);
    Primops.mstore(_97, usr_y_6);
    _98 <- (W256.of_int 484);
    _99 <- (usr_offset + _98);
    tmp114 <@ Primops.calldataload(_99);
    _100 <- tmp114;
    usr_x_7 <- (_100 %% _13);
    _101 <- (W256.of_int 516);
    _102 <- (usr_offset + _101);
    tmp115 <@ Primops.calldataload(_102);
    _103 <- tmp115;
    usr_y_7 <- (_103 %% _13);
    usr_xx_7 <- (PurePrimops.mulmod usr_x_7 usr_x_7 _13);
    _104 <- (PurePrimops.mulmod usr_x_7 usr_xx_7 _13);
    _105 <- (PurePrimops.addmod _104 _19 _13);
    _106 <- (PurePrimops.mulmod usr_y_7 usr_y_7 _13);
    _107 <- (PurePrimops.eq_uint256 _106 _105);
    usr_isValid <- (PurePrimops.bit_and _107 usr_isValid);
    _108 <- (W256.of_int 2304);
    Primops.mstore(_108, usr_x_7);
    _109 <- (W256.of_int 2336);
    Primops.mstore(_109, usr_y_7);
    _110 <- (W256.of_int 548);
    _111 <- (usr_offset + _110);
    tmp116 <@ Primops.calldataload(_111);
    _112 <- tmp116;
    usr_x_8 <- (_112 %% _13);
    _113 <- (W256.of_int 580);
    _114 <- (usr_offset + _113);
    tmp117 <@ Primops.calldataload(_114);
    _115 <- tmp117;
    usr_y_8 <- (_115 %% _13);
    usr_xx_8 <- (PurePrimops.mulmod usr_x_8 usr_x_8 _13);
    _116 <- (PurePrimops.mulmod usr_x_8 usr_xx_8 _13);
    _117 <- (PurePrimops.addmod _116 _19 _13);
    _118 <- (PurePrimops.mulmod usr_y_8 usr_y_8 _13);
    _119 <- (PurePrimops.eq_uint256 _118 _117);
    usr_isValid <- (PurePrimops.bit_and _119 usr_isValid);
    _120 <- (W256.of_int 2368);
    Primops.mstore(_120, usr_x_8);
    _121 <- (W256.of_int 2400);
    Primops.mstore(_121, usr_y_8);
    _122 <- (W256.of_int 612);
    _123 <- (usr_offset + _122);
    tmp118 <@ Primops.calldataload(_123);
    _124 <- tmp118;
    usr_x_9 <- (_124 %% _13);
    _125 <- (W256.of_int 644);
    _126 <- (usr_offset + _125);
    tmp119 <@ Primops.calldataload(_126);
    _127 <- tmp119;
    usr_y_9 <- (_127 %% _13);
    usr_xx_9 <- (PurePrimops.mulmod usr_x_9 usr_x_9 _13);
    _128 <- (PurePrimops.mulmod usr_x_9 usr_xx_9 _13);
    _129 <- (PurePrimops.addmod _128 _19 _13);
    _130 <- (PurePrimops.mulmod usr_y_9 usr_y_9 _13);
    _131 <- (PurePrimops.eq_uint256 _130 _129);
    usr_isValid <- (PurePrimops.bit_and _131 usr_isValid);
    _132 <- (W256.of_int 2432);
    Primops.mstore(_132, usr_x_9);
    _133 <- (W256.of_int 2464);
    Primops.mstore(_133, usr_y_9);
    _134 <- (W256.of_int 676);
    _135 <- (usr_offset + _134);
    tmp120 <@ Primops.calldataload(_135);
    _136 <- tmp120;
    usr_x_10 <- (_136 %% _13);
    _137 <- (W256.of_int 708);
    _138 <- (usr_offset + _137);
    tmp121 <@ Primops.calldataload(_138);
    _139 <- tmp121;
    usr_y_10 <- (_139 %% _13);
    usr_xx_10 <- (PurePrimops.mulmod usr_x_10 usr_x_10 _13);
    _140 <- (PurePrimops.mulmod usr_x_10 usr_xx_10 _13);
    _141 <- (PurePrimops.addmod _140 _19 _13);
    _142 <- (PurePrimops.mulmod usr_y_10 usr_y_10 _13);
    _143 <- (PurePrimops.eq_uint256 _142 _141);
    usr_isValid <- (PurePrimops.bit_and _143 usr_isValid);
    _144 <- (W256.of_int 2496);
    Primops.mstore(_144, usr_x_10);
    _145 <- (W256.of_int 2528);
    Primops.mstore(_145, usr_y_10);
    _146 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _147 <- (W256.of_int 740);
    _148 <- (usr_offset + _147);
    tmp122 <@ Primops.calldataload(_148);
    _149 <- tmp122;
    _150 <- (_149 %% _146);
    _151 <- (W256.of_int 2560);
    Primops.mstore(_151, _150);
    _152 <- (W256.of_int 772);
    _153 <- (usr_offset + _152);
    tmp123 <@ Primops.calldataload(_153);
    _154 <- tmp123;
    _155 <- (_154 %% _146);
    _156 <- (W256.of_int 2592);
    Primops.mstore(_156, _155);
    _157 <- (W256.of_int 804);
    _158 <- (usr_offset + _157);
    tmp124 <@ Primops.calldataload(_158);
    _159 <- tmp124;
    _160 <- (_159 %% _146);
    _161 <- (W256.of_int 2624);
    Primops.mstore(_161, _160);
    _162 <- (W256.of_int 836);
    _163 <- (usr_offset + _162);
    tmp125 <@ Primops.calldataload(_163);
    _164 <- tmp125;
    _165 <- (_164 %% _146);
    _166 <- (W256.of_int 2656);
    Primops.mstore(_166, _165);
    _167 <- (W256.of_int 868);
    _168 <- (usr_offset + _167);
    tmp126 <@ Primops.calldataload(_168);
    _169 <- tmp126;
    _170 <- (_169 %% _146);
    _171 <- (W256.of_int 2688);
    Primops.mstore(_171, _170);
    _172 <- (W256.of_int 900);
    _173 <- (usr_offset + _172);
    tmp127 <@ Primops.calldataload(_173);
    _174 <- tmp127;
    _175 <- (_174 %% _146);
    _176 <- (W256.of_int 2720);
    Primops.mstore(_176, _175);
    _177 <- (W256.of_int 932);
    _178 <- (usr_offset + _177);
    tmp128 <@ Primops.calldataload(_178);
    _179 <- tmp128;
    _180 <- (_179 %% _146);
    _181 <- (W256.of_int 2752);
    Primops.mstore(_181, _180);
    _182 <- (W256.of_int 964);
    _183 <- (usr_offset + _182);
    tmp129 <@ Primops.calldataload(_183);
    _184 <- tmp129;
    _185 <- (_184 %% _146);
    _186 <- (W256.of_int 2784);
    Primops.mstore(_186, _185);
    _187 <- (W256.of_int 996);
    _188 <- (usr_offset + _187);
    tmp130 <@ Primops.calldataload(_188);
    _189 <- tmp130;
    _190 <- (_189 %% _146);
    _191 <- (W256.of_int 2816);
    Primops.mstore(_191, _190);
    _192 <- (W256.of_int 1028);
    _193 <- (usr_offset + _192);
    tmp131 <@ Primops.calldataload(_193);
    _194 <- tmp131;
    _195 <- (_194 %% _146);
    _196 <- (W256.of_int 2848);
    Primops.mstore(_196, _195);
    _197 <- (W256.of_int 1060);
    _198 <- (usr_offset + _197);
    tmp132 <@ Primops.calldataload(_198);
    _199 <- tmp132;
    _200 <- (_199 %% _146);
    _201 <- (W256.of_int 2880);
    Primops.mstore(_201, _200);
    _202 <- (W256.of_int 1092);
    _203 <- (usr_offset + _202);
    tmp133 <@ Primops.calldataload(_203);
    _204 <- tmp133;
    _205 <- (_204 %% _146);
    _206 <- (W256.of_int 2912);
    Primops.mstore(_206, _205);
    _207 <- (W256.of_int 1124);
    _208 <- (usr_offset + _207);
    tmp134 <@ Primops.calldataload(_208);
    _209 <- tmp134;
    _210 <- (_209 %% _146);
    _211 <- (W256.of_int 2944);
    Primops.mstore(_211, _210);
    _212 <- (W256.of_int 1156);
    _213 <- (usr_offset + _212);
    tmp135 <@ Primops.calldataload(_213);
    _214 <- tmp135;
    _215 <- (_214 %% _146);
    _216 <- (W256.of_int 2976);
    Primops.mstore(_216, _215);
    _217 <- (W256.of_int 1188);
    _218 <- (usr_offset + _217);
    tmp136 <@ Primops.calldataload(_218);
    _219 <- tmp136;
    _220 <- (_219 %% _146);
    _221 <- (W256.of_int 3008);
    Primops.mstore(_221, _220);
    _222 <- (W256.of_int 1220);
    _223 <- (usr_offset + _222);
    tmp137 <@ Primops.calldataload(_223);
    _224 <- tmp137;
    _225 <- (_224 %% _146);
    _226 <- (W256.of_int 3040);
    Primops.mstore(_226, _225);
    _227 <- (W256.of_int 1252);
    _228 <- (usr_offset + _227);
    tmp138 <@ Primops.calldataload(_228);
    _229 <- tmp138;
    _230 <- (_229 %% _146);
    _231 <- (W256.of_int 3072);
    Primops.mstore(_231, _230);
    _232 <- (W256.of_int 1284);
    _233 <- (usr_offset + _232);
    tmp139 <@ Primops.calldataload(_233);
    _234 <- tmp139;
    _235 <- (_234 %% _146);
    _236 <- (W256.of_int 3104);
    Primops.mstore(_236, _235);
    _237 <- (W256.of_int 1316);
    _238 <- (usr_offset + _237);
    tmp140 <@ Primops.calldataload(_238);
    _239 <- tmp140;
    usr_x_11 <- (_239 %% _13);
    _240 <- (W256.of_int 1348);
    _241 <- (usr_offset + _240);
    tmp141 <@ Primops.calldataload(_241);
    _242 <- tmp141;
    usr_y_11 <- (_242 %% _13);
    usr_xx_11 <- (PurePrimops.mulmod usr_x_11 usr_x_11 _13);
    _243 <- (PurePrimops.mulmod usr_x_11 usr_xx_11 _13);
    _244 <- (PurePrimops.addmod _243 _19 _13);
    _245 <- (PurePrimops.mulmod usr_y_11 usr_y_11 _13);
    _246 <- (PurePrimops.eq_uint256 _245 _244);
    usr_isValid <- (PurePrimops.bit_and _246 usr_isValid);
    _247 <- (W256.of_int 3136);
    Primops.mstore(_247, usr_x_11);
    _248 <- (W256.of_int 3168);
    Primops.mstore(_248, usr_y_11);
    _249 <- (W256.of_int 1380);
    _250 <- (usr_offset + _249);
    tmp142 <@ Primops.calldataload(_250);
    _251 <- tmp142;
    usr_x_12 <- (_251 %% _13);
    _252 <- (W256.of_int 1412);
    _253 <- (usr_offset + _252);
    tmp143 <@ Primops.calldataload(_253);
    _254 <- tmp143;
    usr_y_12 <- (_254 %% _13);
    usr_xx_12 <- (PurePrimops.mulmod usr_x_12 usr_x_12 _13);
    _255 <- (PurePrimops.mulmod usr_x_12 usr_xx_12 _13);
    _256 <- (PurePrimops.addmod _255 _19 _13);
    _257 <- (PurePrimops.mulmod usr_y_12 usr_y_12 _13);
    _258 <- (PurePrimops.eq_uint256 _257 _256);
    usr_isValid <- (PurePrimops.bit_and _258 usr_isValid);
    _259 <- (W256.of_int 3200);
    Primops.mstore(_259, usr_x_12);
    _260 <- (W256.of_int 3232);
    Primops.mstore(_260, usr_y_12);
    tmp144 <@ Primops.calldataload(_16);
    usr_offset <- tmp144;
    _261 <- (usr_offset + _1);
    tmp145 <@ Primops.calldataload(_261);
    usr_recursiveProofLengthInWords <- tmp145;
    _262 <- (W256.of_int 1792);
    tmp146 <@ Primops.mload(_262);
    _263 <- tmp146;
    tmp147 <- _263;
    if ((tmp147 = (W256.of_int 0)))
      {
      _264 <- (PurePrimops.iszero usr_recursiveProofLengthInWords);
      usr_isValid <- (PurePrimops.bit_and _264 usr_isValid);
      
      }
    
    else {
      _265 <- (PurePrimops.eq_uint256 usr_recursiveProofLengthInWords _1);
      usr_isValid <- (PurePrimops.bit_and _265 usr_isValid);
      _266 <- (usr_offset + _5);
      tmp148 <@ Primops.calldataload(_266);
      _267 <- tmp148;
      usr_x_13 <- (_267 %% _13);
      _268 <- (usr_offset + _16);
      tmp149 <@ Primops.calldataload(_268);
      _269 <- tmp149;
      usr_y_13 <- (_269 %% _13);
      usr_xx_13 <- (PurePrimops.mulmod usr_x_13 usr_x_13 _13);
      _270 <- (PurePrimops.mulmod usr_x_13 usr_xx_13 _13);
      _271 <- (PurePrimops.addmod _270 _19 _13);
      _272 <- (PurePrimops.mulmod usr_y_13 usr_y_13 _13);
      _273 <- (PurePrimops.eq_uint256 _272 _271);
      usr_isValid <- (PurePrimops.bit_and _273 usr_isValid);
      _274 <- (W256.of_int 3264);
      Primops.mstore(_274, usr_x_13);
      _275 <- (W256.of_int 3296);
      Primops.mstore(_275, usr_y_13);
      _276 <- (usr_offset + _26);
      tmp150 <@ Primops.calldataload(_276);
      _277 <- tmp150;
      usr_x_14 <- (_277 %% _13);
      _278 <- (usr_offset + _29);
      tmp151 <@ Primops.calldataload(_278);
      _279 <- tmp151;
      usr_y_14 <- (_279 %% _13);
      usr_xx_14 <- (PurePrimops.mulmod usr_x_14 usr_x_14 _13);
      _280 <- (PurePrimops.mulmod usr_x_14 usr_xx_14 _13);
      _281 <- (PurePrimops.addmod _280 _19 _13);
      _282 <- (PurePrimops.mulmod usr_y_14 usr_y_14 _13);
      _283 <- (PurePrimops.eq_uint256 _282 _281);
      usr_isValid <- (PurePrimops.bit_and _283 usr_isValid);
      _284 <- (W256.of_int 3328);
      Primops.mstore(_284, usr_x_14);
      _285 <- (W256.of_int 3360);
      Primops.mstore(_285, usr_y_14);
      
      }
    
    _286 <- (PurePrimops.iszero usr_isValid);
    if ((bool_of_uint256 _286))
      {
      _287 <- (W256.of_int STRING (*loadProof: Proof is invalid*));
      _288 <- (W256.of_int 27);
      tmp152 <@ usr_revertWithMessage(_288, _287);
      
      }
    
    }
  
  proc usr_pointAddIntoDest(usr_p1 : uint256, usr_p2 : uint256, usr_dest : uint256): unit = {
    var _1, tmp58, _2, _3, _4, _5, tmp59, _6, tmp60, _7, _8, _9, tmp61, _10, _11, _12, _13, tmp62, _14, tmp63, _15, _16, _17, tmp64;
    tmp58 <@ Primops.mload(usr_p1);
    _1 <- tmp58;
    _2 <- (W256.of_int 0);
    Primops.mstore(_2, _1);
    _3 <- (W256.of_int 32);
    _4 <- (usr_p1 + _3);
    tmp59 <@ Primops.mload(_4);
    _5 <- tmp59;
    Primops.mstore(_3, _5);
    tmp60 <@ Primops.mload(usr_p2);
    _6 <- tmp60;
    _7 <- (W256.of_int 64);
    Primops.mstore(_7, _6);
    _8 <- (usr_p2 + _3);
    tmp61 <@ Primops.mload(_8);
    _9 <- tmp61;
    _10 <- (W256.of_int 96);
    Primops.mstore(_10, _9);
    _11 <- (W256.of_int 128);
    _12 <- (W256.of_int 6);
    tmp62 <@ Primops.gas();
    _13 <- tmp62;
    tmp63 <@ Primops.staticcall(_13, _12, _2, _11, usr_dest, _7);
    _14 <- tmp63;
    _15 <- (PurePrimops.iszero _14);
    if ((bool_of_uint256 _15))
      {
      _16 <- (W256.of_int STRING (*pointAddIntoDest: ecAdd failed*));
      _17 <- (W256.of_int 30);
      tmp64 <@ usr_revertWithMessage(_17, _16);
      
      }
    
    }
  
  proc abi_encode_bytes32_to_bytes32(value : uint256, pos : uint256): unit = {
    var _1;
    _1 <- (cleanup_bytes32 value);
    Primops.mstore(pos, _1);
    }
  
  proc constructor_Verifier(): unit = {
    var tmp8;
    tmp8 <@ constructor_IVerifier();
    }
  
  proc usr_pointSubAssign(usr_p1 : uint256, usr_p2 : uint256): unit = {
    var _1, tmp65, _2, _3, _4, _5, tmp66, _6, tmp67, _7, _8, _9, tmp68, _10, _11, _12, _13, _14, _15, tmp69, _16, tmp70, _17, _18, _19, tmp71;
    tmp65 <@ Primops.mload(usr_p1);
    _1 <- tmp65;
    _2 <- (W256.of_int 0);
    Primops.mstore(_2, _1);
    _3 <- (W256.of_int 32);
    _4 <- (usr_p1 + _3);
    tmp66 <@ Primops.mload(_4);
    _5 <- tmp66;
    Primops.mstore(_3, _5);
    tmp67 <@ Primops.mload(usr_p2);
    _6 <- tmp67;
    _7 <- (W256.of_int 64);
    Primops.mstore(_7, _6);
    _8 <- (usr_p2 + _3);
    tmp68 <@ Primops.mload(_8);
    _9 <- tmp68;
    _10 <- (W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583);
    _11 <- (_10 - _9);
    _12 <- (W256.of_int 96);
    Primops.mstore(_12, _11);
    _13 <- (W256.of_int 128);
    _14 <- (W256.of_int 6);
    tmp69 <@ Primops.gas();
    _15 <- tmp69;
    tmp70 <@ Primops.staticcall(_15, _14, _2, _13, usr_p1, _7);
    _16 <- tmp70;
    _17 <- (PurePrimops.iszero _16);
    if ((bool_of_uint256 _17))
      {
      _18 <- (W256.of_int STRING (*pointSubAssign: ecAdd failed*));
      _19 <- (W256.of_int 28);
      tmp71 <@ usr_revertWithMessage(_19, _18);
      
      }
    
    }
  
  proc usr_pointNegate(usr_point : uint256): unit = {
    var _1, _2, usr_pY, tmp88, tmp89, _3, tmp90, _4, _5, tmp91, _6, _7;
    _1 <- (W256.of_int 32);
    _2 <- (usr_point + _1);
    tmp88 <@ Primops.mload(_2);
    usr_pY <- tmp88;
    tmp89 <- usr_pY;
    if ((tmp89 = (W256.of_int 0)))
      {
      tmp90 <@ Primops.mload(usr_point);
      _3 <- tmp90;
      if ((bool_of_uint256 _3))
        {
        _4 <- (W256.of_int STRING (*pointNegate: invalid point*));
        _5 <- (W256.of_int 26);
        tmp91 <@ usr_revertWithMessage(_5, _4);
        
        }
      
      
      }
    
    else {
      _6 <- (W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583);
      _7 <- (_6 - usr_pY);
      Primops.mstore(_2, _7);
      
      }
    
    }
  
  proc usr_pointMulAndAddIntoDest(usr_point : uint256, usr_s : uint256, usr_dest : uint256): unit = {
    var _1, tmp79, _2, _3, _4, _5, tmp80, _6, _7, _8, _9, tmp81, usr_success, tmp82, _10, tmp83, _11, _12, tmp84, _13, _14, _15, tmp85, _16, tmp86, _17, _18, _19, tmp87;
    tmp79 <@ Primops.mload(usr_point);
    _1 <- tmp79;
    _2 <- (W256.of_int 0);
    Primops.mstore(_2, _1);
    _3 <- (W256.of_int 32);
    _4 <- (usr_point + _3);
    tmp80 <@ Primops.mload(_4);
    _5 <- tmp80;
    Primops.mstore(_3, _5);
    _6 <- (W256.of_int 64);
    Primops.mstore(_6, usr_s);
    _7 <- (W256.of_int 96);
    _8 <- (W256.of_int 7);
    tmp81 <@ Primops.gas();
    _9 <- tmp81;
    tmp82 <@ Primops.staticcall(_9, _8, _2, _7, _2, _6);
    usr_success <- tmp82;
    tmp83 <@ Primops.mload(usr_dest);
    _10 <- tmp83;
    Primops.mstore(_6, _10);
    _11 <- (usr_dest + _3);
    tmp84 <@ Primops.mload(_11);
    _12 <- tmp84;
    Primops.mstore(_7, _12);
    _13 <- (W256.of_int 128);
    _14 <- (W256.of_int 6);
    tmp85 <@ Primops.gas();
    _15 <- tmp85;
    tmp86 <@ Primops.staticcall(_15, _14, _2, _13, usr_dest, _6);
    _16 <- tmp86;
    usr_success <- (PurePrimops.bit_and usr_success _16);
    _17 <- (PurePrimops.iszero usr_success);
    if ((bool_of_uint256 _17))
      {
      _18 <- (W256.of_int STRING (*pointMulAndAddIntoDest*));
      _19 <- (W256.of_int 22);
      tmp87 <@ usr_revertWithMessage(_19, _18);
      
      }
    
    }
  
  proc abi_encode_bool_to_bool(value : uint256, pos : uint256): unit = {
    var _1, tmp31;
    tmp31 <@ cleanup_bool(value);
    _1 <- tmp31;
    Primops.mstore(pos, _1);
    }
  
  proc fun_verificationKeyHash(): uint256 = {
    var var_vkHash, tmp47, usr_start, usr_end, _1, _2, usr_length, tmp48;
    tmp47 <@ fun_loadVerificationKey();
    usr_start <- (W256.of_int 512);
    usr_end <- (W256.of_int 1792);
    _1 <- (W256.of_int 32);
    _2 <- (usr_end - usr_start);
    usr_length <- (_2 + _1);
    tmp48 <@ Primops.keccak256(usr_start, usr_length);
    var_vkHash <- tmp48;
    return var_vkHash;
    }
  
  proc usr_modexp(usr_value : uint256, usr_power : uint256): uint256 = {
    var usr_res, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, tmp49, _11, tmp50, _12, _13, _14, tmp51, tmp52;
    _1 <- (W256.of_int 32);
    _2 <- (W256.of_int 0);
    Primops.mstore(_2, _1);
    Primops.mstore(_1, _1);
    _3 <- (W256.of_int 64);
    Primops.mstore(_3, _1);
    _4 <- (W256.of_int 96);
    Primops.mstore(_4, usr_value);
    _5 <- (W256.of_int 128);
    Primops.mstore(_5, usr_power);
    _6 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _7 <- (W256.of_int 160);
    Primops.mstore(_7, _6);
    _8 <- (W256.of_int 192);
    _9 <- (W256.of_int 5);
    tmp49 <@ Primops.gas();
    _10 <- tmp49;
    tmp50 <@ Primops.staticcall(_10, _9, _2, _8, _2, _1);
    _11 <- tmp50;
    _12 <- (PurePrimops.iszero _11);
    if ((bool_of_uint256 _12))
      {
      _13 <- (W256.of_int STRING (*modexp precompile failed*));
      _14 <- (W256.of_int 24);
      tmp51 <@ usr_revertWithMessage(_14, _13);
      
      }
    
    tmp52 <@ Primops.mload(_2);
    usr_res <- tmp52;
    return usr_res;
    }
  
  proc abi_decode_array_uint256_dyn_calldata(offset : uint256, _end : uint256): (uint256 * uint256) = {
    var arrayPos, length, _1, _2, _3, _4, tmp17, tmp18, _5, _6, tmp19, _7, _8, _9, _10, tmp20;
    _1 <- (W256.of_int 31);
    _2 <- (offset + _1);
    _3 <- (PurePrimops.slt_uint256 _2 _end);
    _4 <- (PurePrimops.iszero _3);
    if ((bool_of_uint256 _4))
      {
      tmp17 <@ revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d();
      
      }
    
    tmp18 <@ Primops.calldataload(offset);
    length <- tmp18;
    _5 <- (W256.of_int 18446744073709551615);
    _6 <- (PurePrimops.gt_uint256 length _5);
    if ((bool_of_uint256 _6))
      {
      tmp19 <@ revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490();
      
      }
    
    _7 <- (W256.of_int 32);
    arrayPos <- (offset + _7);
    _8 <- (length * _7);
    _9 <- (arrayPos + _8);
    _10 <- (PurePrimops.gt_uint256 _9 _end);
    if ((bool_of_uint256 _10))
      {
      tmp20 <@ revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef();
      
      }
    
    return (arrayPos, length);
    }
  
  proc abi_decode(headStart : uint256, dataEnd : uint256): unit = {
    var _1, _2, _3, tmp38;
    _1 <- (W256.of_int 0);
    _2 <- (dataEnd - headStart);
    _3 <- (PurePrimops.slt_uint256 _2 _1);
    if ((bool_of_uint256 _3))
      {
      tmp38 <@ revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b();
      
      }
    
    }
  
  proc usr_initializeTranscript(): unit = {
    var _1, _2, tmp153, tmp154, _3, _4, tmp155, tmp156, _5, _6, tmp157, tmp158, _7, _8, tmp159, tmp160, _9, _10, tmp161, tmp162, _11, _12, tmp163, tmp164, _13, _14, tmp165, tmp166, _15, _16, tmp167, tmp168, _17, _18, tmp169, tmp170, _19, _20, tmp171, _21, _22, _23, tmp172, tmp173, _24, _25, tmp174, tmp175, _26, _27, tmp176, _28, _29, _30, tmp177, _31, _32, _33, tmp178, tmp179, _34, _35, tmp180, tmp181, _36, _37, tmp182, _38, _39, _40, tmp183, _41, _42, _43, tmp184, tmp185, _44, _45, tmp186, tmp187, _46, _47, tmp188, _48, _49, _50, tmp189, tmp190, _51, _52, tmp191, tmp192, _53, _54, tmp193, tmp194, _55, _56, tmp195, tmp196, _57, _58, tmp197, tmp198, _59, _60, tmp199, tmp200, _61, _62, tmp201, tmp202, _63, _64, tmp203, tmp204, _65, usr_z, tmp205, _66, _67, _68, tmp206, _69, _70, _71, tmp207, tmp208, _72, _73, tmp209, tmp210, _74, _75, tmp211, tmp212, _76, _77, tmp213, tmp214, _78, _79, tmp215, tmp216, _80, _81, tmp217, tmp218, _82, _83, tmp219, tmp220, _84, _85, tmp221, tmp222, _86, _87, tmp223, tmp224, _88, _89, tmp225, tmp226, _90, _91, tmp227, tmp228, _92, _93, tmp229, tmp230, _94, _95, tmp231, tmp232, _96, _97, tmp233, tmp234, _98, _99, tmp235, tmp236, _100, _101, tmp237, tmp238, _102, _103, tmp239, tmp240, _104, _105, tmp241, tmp242, _106, _107, tmp243, _108, _109, _110, tmp244, tmp245, _111, _112, tmp246, tmp247, _113, _114, tmp248, tmp249, _115, _116, tmp250, tmp251, _117, _118, tmp252, _119;
    _1 <- (W256.of_int 1824);
    tmp153 <@ Primops.mload(_1);
    _2 <- tmp153;
    tmp154 <@ usr_updateTranscript(_2);
    _3 <- (W256.of_int 1856);
    tmp155 <@ Primops.mload(_3);
    _4 <- tmp155;
    tmp156 <@ usr_updateTranscript(_4);
    _5 <- (W256.of_int 1888);
    tmp157 <@ Primops.mload(_5);
    _6 <- tmp157;
    tmp158 <@ usr_updateTranscript(_6);
    _7 <- (W256.of_int 1920);
    tmp159 <@ Primops.mload(_7);
    _8 <- tmp159;
    tmp160 <@ usr_updateTranscript(_8);
    _9 <- (W256.of_int 1952);
    tmp161 <@ Primops.mload(_9);
    _10 <- tmp161;
    tmp162 <@ usr_updateTranscript(_10);
    _11 <- (W256.of_int 1984);
    tmp163 <@ Primops.mload(_11);
    _12 <- tmp163;
    tmp164 <@ usr_updateTranscript(_12);
    _13 <- (W256.of_int 2016);
    tmp165 <@ Primops.mload(_13);
    _14 <- tmp165;
    tmp166 <@ usr_updateTranscript(_14);
    _15 <- (W256.of_int 2048);
    tmp167 <@ Primops.mload(_15);
    _16 <- tmp167;
    tmp168 <@ usr_updateTranscript(_16);
    _17 <- (W256.of_int 2080);
    tmp169 <@ Primops.mload(_17);
    _18 <- tmp169;
    tmp170 <@ usr_updateTranscript(_18);
    _19 <- (W256.of_int 0);
    tmp171 <@ usr_getTranscriptChallenge(_19);
    _20 <- tmp171;
    _21 <- (W256.of_int 3840);
    Primops.mstore(_21, _20);
    _22 <- (W256.of_int 2176);
    tmp172 <@ Primops.mload(_22);
    _23 <- tmp172;
    tmp173 <@ usr_updateTranscript(_23);
    _24 <- (W256.of_int 2208);
    tmp174 <@ Primops.mload(_24);
    _25 <- tmp174;
    tmp175 <@ usr_updateTranscript(_25);
    _26 <- (W256.of_int 1);
    tmp176 <@ usr_getTranscriptChallenge(_26);
    _27 <- tmp176;
    _28 <- (W256.of_int 3552);
    Primops.mstore(_28, _27);
    _29 <- (W256.of_int 2);
    tmp177 <@ usr_getTranscriptChallenge(_29);
    _30 <- tmp177;
    _31 <- (W256.of_int 3584);
    Primops.mstore(_31, _30);
    _32 <- (W256.of_int 2112);
    tmp178 <@ Primops.mload(_32);
    _33 <- tmp178;
    tmp179 <@ usr_updateTranscript(_33);
    _34 <- (W256.of_int 2144);
    tmp180 <@ Primops.mload(_34);
    _35 <- tmp180;
    tmp181 <@ usr_updateTranscript(_35);
    _36 <- (W256.of_int 3);
    tmp182 <@ usr_getTranscriptChallenge(_36);
    _37 <- tmp182;
    _38 <- (W256.of_int 3872);
    Primops.mstore(_38, _37);
    _39 <- (W256.of_int 4);
    tmp183 <@ usr_getTranscriptChallenge(_39);
    _40 <- tmp183;
    _41 <- (W256.of_int 3904);
    Primops.mstore(_41, _40);
    _42 <- (W256.of_int 2240);
    tmp184 <@ Primops.mload(_42);
    _43 <- tmp184;
    tmp185 <@ usr_updateTranscript(_43);
    _44 <- (W256.of_int 2272);
    tmp186 <@ Primops.mload(_44);
    _45 <- tmp186;
    tmp187 <@ usr_updateTranscript(_45);
    _46 <- (W256.of_int 5);
    tmp188 <@ usr_getTranscriptChallenge(_46);
    _47 <- tmp188;
    _48 <- (W256.of_int 3520);
    Primops.mstore(_48, _47);
    _49 <- (W256.of_int 2304);
    tmp189 <@ Primops.mload(_49);
    _50 <- tmp189;
    tmp190 <@ usr_updateTranscript(_50);
    _51 <- (W256.of_int 2336);
    tmp191 <@ Primops.mload(_51);
    _52 <- tmp191;
    tmp192 <@ usr_updateTranscript(_52);
    _53 <- (W256.of_int 2368);
    tmp193 <@ Primops.mload(_53);
    _54 <- tmp193;
    tmp194 <@ usr_updateTranscript(_54);
    _55 <- (W256.of_int 2400);
    tmp195 <@ Primops.mload(_55);
    _56 <- tmp195;
    tmp196 <@ usr_updateTranscript(_56);
    _57 <- (W256.of_int 2432);
    tmp197 <@ Primops.mload(_57);
    _58 <- tmp197;
    tmp198 <@ usr_updateTranscript(_58);
    _59 <- (W256.of_int 2464);
    tmp199 <@ Primops.mload(_59);
    _60 <- tmp199;
    tmp200 <@ usr_updateTranscript(_60);
    _61 <- (W256.of_int 2496);
    tmp201 <@ Primops.mload(_61);
    _62 <- tmp201;
    tmp202 <@ usr_updateTranscript(_62);
    _63 <- (W256.of_int 2528);
    tmp203 <@ Primops.mload(_63);
    _64 <- tmp203;
    tmp204 <@ usr_updateTranscript(_64);
    _65 <- (W256.of_int 6);
    tmp205 <@ usr_getTranscriptChallenge(_65);
    usr_z <- tmp205;
    _66 <- (W256.of_int 4064);
    Primops.mstore(_66, usr_z);
    _67 <- (W256.of_int 67108864);
    tmp206 <@ usr_modexp(usr_z, _67);
    _68 <- tmp206;
    _69 <- (W256.of_int 4192);
    Primops.mstore(_69, _68);
    _70 <- (W256.of_int 3072);
    tmp207 <@ Primops.mload(_70);
    _71 <- tmp207;
    tmp208 <@ usr_updateTranscript(_71);
    _72 <- (W256.of_int 2560);
    tmp209 <@ Primops.mload(_72);
    _73 <- tmp209;
    tmp210 <@ usr_updateTranscript(_73);
    _74 <- (W256.of_int 2592);
    tmp211 <@ Primops.mload(_74);
    _75 <- tmp211;
    tmp212 <@ usr_updateTranscript(_75);
    _76 <- (W256.of_int 2624);
    tmp213 <@ Primops.mload(_76);
    _77 <- tmp213;
    tmp214 <@ usr_updateTranscript(_77);
    _78 <- (W256.of_int 2656);
    tmp215 <@ Primops.mload(_78);
    _79 <- tmp215;
    tmp216 <@ usr_updateTranscript(_79);
    _80 <- (W256.of_int 2688);
    tmp217 <@ Primops.mload(_80);
    _81 <- tmp217;
    tmp218 <@ usr_updateTranscript(_81);
    _82 <- (W256.of_int 2720);
    tmp219 <@ Primops.mload(_82);
    _83 <- tmp219;
    tmp220 <@ usr_updateTranscript(_83);
    _84 <- (W256.of_int 2752);
    tmp221 <@ Primops.mload(_84);
    _85 <- tmp221;
    tmp222 <@ usr_updateTranscript(_85);
    _86 <- (W256.of_int 2784);
    tmp223 <@ Primops.mload(_86);
    _87 <- tmp223;
    tmp224 <@ usr_updateTranscript(_87);
    _88 <- (W256.of_int 2816);
    tmp225 <@ Primops.mload(_88);
    _89 <- tmp225;
    tmp226 <@ usr_updateTranscript(_89);
    _90 <- (W256.of_int 2848);
    tmp227 <@ Primops.mload(_90);
    _91 <- tmp227;
    tmp228 <@ usr_updateTranscript(_91);
    _92 <- (W256.of_int 2944);
    tmp229 <@ Primops.mload(_92);
    _93 <- tmp229;
    tmp230 <@ usr_updateTranscript(_93);
    _94 <- (W256.of_int 3008);
    tmp231 <@ Primops.mload(_94);
    _95 <- tmp231;
    tmp232 <@ usr_updateTranscript(_95);
    _96 <- (W256.of_int 3040);
    tmp233 <@ Primops.mload(_96);
    _97 <- tmp233;
    tmp234 <@ usr_updateTranscript(_97);
    _98 <- (W256.of_int 2880);
    tmp235 <@ Primops.mload(_98);
    _99 <- tmp235;
    tmp236 <@ usr_updateTranscript(_99);
    _100 <- (W256.of_int 2912);
    tmp237 <@ Primops.mload(_100);
    _101 <- tmp237;
    tmp238 <@ usr_updateTranscript(_101);
    _102 <- (W256.of_int 2976);
    tmp239 <@ Primops.mload(_102);
    _103 <- tmp239;
    tmp240 <@ usr_updateTranscript(_103);
    _104 <- (W256.of_int 3104);
    tmp241 <@ Primops.mload(_104);
    _105 <- tmp241;
    tmp242 <@ usr_updateTranscript(_105);
    _106 <- (W256.of_int 7);
    tmp243 <@ usr_getTranscriptChallenge(_106);
    _107 <- tmp243;
    _108 <- (W256.of_int 4000);
    Primops.mstore(_108, _107);
    _109 <- (W256.of_int 3136);
    tmp244 <@ Primops.mload(_109);
    _110 <- tmp244;
    tmp245 <@ usr_updateTranscript(_110);
    _111 <- (W256.of_int 3168);
    tmp246 <@ Primops.mload(_111);
    _112 <- tmp246;
    tmp247 <@ usr_updateTranscript(_112);
    _113 <- (W256.of_int 3200);
    tmp248 <@ Primops.mload(_113);
    _114 <- tmp248;
    tmp249 <@ usr_updateTranscript(_114);
    _115 <- (W256.of_int 3232);
    tmp250 <@ Primops.mload(_115);
    _116 <- tmp250;
    tmp251 <@ usr_updateTranscript(_116);
    _117 <- (W256.of_int 8);
    tmp252 <@ usr_getTranscriptChallenge(_117);
    _118 <- tmp252;
    _119 <- (W256.of_int 4032);
    Primops.mstore(_119, _118);
    }
  
  proc usr_addAssignPermutationLinearisationContributionWithV(usr_dest : uint256, usr_stateOpening0AtZ : uint256, usr_stateOpening1AtZ : uint256, usr_stateOpening2AtZ : uint256, usr_stateOpening3AtZ : uint256): unit = {
    var usr_factor, tmp312, _1, tmp313, _2, _3, tmp314, usr_gamma, tmp315, _4, usr_intermediateValue, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, usr_l0AtZ, tmp316, _15, _16, tmp317, _17, _18, tmp318, _19, _20, tmp319, _21, tmp320, _22, _23, tmp321, usr_beta, tmp322, usr_gamma_1, tmp323, _24, _25, tmp324, _26, _27, usr_intermediateValue_1, _28, _29, tmp325, _30, _31, _32, _33, tmp326, _34, _35, _36, tmp327, _37, _38, tmp328, tmp329;
    tmp312 <@ Primops.mload((W256.of_int 3680));
    usr_factor <- tmp312;
    tmp313 <@ Primops.mload((W256.of_int 3552));
    _1 <- tmp313;
    _2 <- (W256.of_int 4064);
    tmp314 <@ Primops.mload(_2);
    _3 <- tmp314;
    tmp315 <@ Primops.mload((W256.of_int 3584));
    usr_gamma <- tmp315;
    _4 <- (PurePrimops.addmod (PurePrimops.mulmod _3 _1 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617)) usr_gamma (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_intermediateValue <- (PurePrimops.addmod _4 usr_stateOpening0AtZ (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.mulmod usr_factor usr_intermediateValue (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _5 <- (W256.of_int 5);
    _6 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617)) _5 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _7 <- (PurePrimops.addmod _6 usr_gamma (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_intermediateValue <- (PurePrimops.addmod _7 usr_stateOpening1AtZ (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.mulmod usr_factor usr_intermediateValue (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _8 <- (W256.of_int 7);
    _9 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617)) _8 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _10 <- (PurePrimops.addmod _9 usr_gamma (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_intermediateValue <- (PurePrimops.addmod _10 usr_stateOpening2AtZ (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.mulmod usr_factor usr_intermediateValue (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _11 <- (W256.of_int 10);
    _12 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617)) _11 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _13 <- (PurePrimops.addmod _12 usr_gamma (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_intermediateValue <- (PurePrimops.addmod _13 usr_stateOpening3AtZ (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.mulmod usr_factor usr_intermediateValue (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _14 <- (W256.of_int 4128);
    tmp316 <@ Primops.mload(_14);
    usr_l0AtZ <- tmp316;
    _15 <- (W256.of_int 3712);
    tmp317 <@ Primops.mload(_15);
    _16 <- tmp317;
    _17 <- (PurePrimops.mulmod usr_l0AtZ _16 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.addmod usr_factor _17 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    tmp318 <@ Primops.mload((W256.of_int 4000));
    _18 <- tmp318;
    usr_factor <- (PurePrimops.mulmod usr_factor _18 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _19 <- (W256.of_int 4928);
    Primops.mstore(_19, usr_factor);
    tmp319 <@ Primops.mload((W256.of_int 3552));
    _20 <- tmp319;
    tmp320 <@ Primops.mload((W256.of_int 3680));
    _21 <- tmp320;
    usr_factor <- (PurePrimops.mulmod _21 _20 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _22 <- (W256.of_int 2848);
    tmp321 <@ Primops.mload(_22);
    _23 <- tmp321;
    usr_factor <- (PurePrimops.mulmod usr_factor _23 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    tmp322 <@ Primops.mload((W256.of_int 3552));
    usr_beta <- tmp322;
    tmp323 <@ Primops.mload((W256.of_int 3584));
    usr_gamma_1 <- tmp323;
    _24 <- (W256.of_int 2752);
    tmp324 <@ Primops.mload(_24);
    _25 <- tmp324;
    _26 <- (PurePrimops.mulmod _25 usr_beta (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _27 <- (PurePrimops.addmod _26 usr_gamma_1 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_intermediateValue_1 <- (PurePrimops.addmod _27 usr_stateOpening0AtZ (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.mulmod usr_factor usr_intermediateValue_1 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _28 <- (W256.of_int 2784);
    tmp325 <@ Primops.mload(_28);
    _29 <- tmp325;
    _30 <- (PurePrimops.mulmod _29 usr_beta (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _31 <- (PurePrimops.addmod _30 usr_gamma_1 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_intermediateValue_1 <- (PurePrimops.addmod _31 usr_stateOpening1AtZ (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.mulmod usr_factor usr_intermediateValue_1 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _32 <- (W256.of_int 2816);
    tmp326 <@ Primops.mload(_32);
    _33 <- tmp326;
    _34 <- (PurePrimops.mulmod _33 usr_beta (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _35 <- (PurePrimops.addmod _34 usr_gamma_1 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_intermediateValue_1 <- (PurePrimops.addmod _35 usr_stateOpening2AtZ (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    usr_factor <- (PurePrimops.mulmod usr_factor usr_intermediateValue_1 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    tmp327 <@ Primops.mload((W256.of_int 4000));
    _36 <- tmp327;
    usr_factor <- (PurePrimops.mulmod usr_factor _36 (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617));
    _37 <- (W256.of_int 4224);
    _38 <- (W256.of_int 1344);
    tmp328 <@ usr_pointMulIntoDest(_38, usr_factor, _37);
    tmp329 <@ usr_pointSubAssign(usr_dest, _37);
    }
  
  (* proc _BODY(): unit = { *)
  (*   tmp0 <@ memoryguard((W256.of_int 128)); *)
  (*   _1 <- tmp0; *)
  (*   _2 <- (W256.of_int 64); *)
  (*   Primops.mstore(_2, _1); *)
  (*   tmp1 <@ callvalue(); *)
  (*   _3 <- tmp1; *)
  (*   if ((bool_of_uint256 _3)) *)
  (*     { *)
  (*     tmp2 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(); *)
      
  (*     } *)
    
  (*   tmp3 <@ constructor_Verifier(); *)
  (*   tmp4 <@ allocate_unbounded(); *)
  (*   _4 <- tmp4; *)
  (*   tmp5 <@ datasize((W256.of_int STRING (*Verifier_1261_deployed*))); *)
  (*   _5 <- tmp5; *)
  (*   tmp6 <@ dataoffset((W256.of_int STRING (*Verifier_1261_deployed*))); *)
  (*   _6 <- tmp6; *)
  (*   codecopy(_4, _6, _5); *)
  (*   _7 <- _5; *)
  (*   Primops.evm_return(_4, _5); *)
  (*   } *)
  
  proc abi_decode_array_uint256_dyn_calldatat_array_uint256_dyn_calldatat_array_uint256_dyn_calldata(headStart : uint256, dataEnd : uint256): (uint256 * uint256 * uint256 * uint256 * uint256 * uint256) = {
    var value0, value1, value2, value3, value4, value5, _1, _2, _3, tmp21, _4, _5, offset, tmp22, _6, _7, tmp23, _8, tmp24, _9, _10, offset_1, tmp25, _11, tmp26, _12, tmp27, _13, _14, offset_2, tmp28, _15, tmp29, _16, tmp30;
    _1 <- (W256.of_int 96);
    _2 <- (dataEnd - headStart);
    _3 <- (PurePrimops.slt_uint256 _2 _1);
    if ((bool_of_uint256 _3))
      {
      tmp21 <@ revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b();
      
      }
    
    _4 <- (W256.of_int 0);
    _5 <- (headStart + _4);
    tmp22 <@ Primops.calldataload(_5);
    offset <- tmp22;
    _6 <- (W256.of_int 18446744073709551615);
    _7 <- (PurePrimops.gt_uint256 offset _6);
    if ((bool_of_uint256 _7))
      {
      tmp23 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
      
      }
    
    _8 <- (headStart + offset);
    tmp24 <@ abi_decode_array_uint256_dyn_calldata(_8, dataEnd);
    (value0,value1) <- tmp24;
    _9 <- (W256.of_int 32);
    _10 <- (headStart + _9);
    tmp25 <@ Primops.calldataload(_10);
    offset_1 <- tmp25;
    _11 <- (PurePrimops.gt_uint256 offset_1 _6);
    if ((bool_of_uint256 _11))
      {
      tmp26 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
      
      }
    
    _12 <- (headStart + offset_1);
    tmp27 <@ abi_decode_array_uint256_dyn_calldata(_12, dataEnd);
    (value2,value3) <- tmp27;
    _13 <- (W256.of_int 64);
    _14 <- (headStart + _13);
    tmp28 <@ Primops.calldataload(_14);
    offset_2 <- tmp28;
    _15 <- (PurePrimops.gt_uint256 offset_2 _6);
    if ((bool_of_uint256 _15))
      {
      tmp29 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
      
      }
    
    _16 <- (headStart + offset_2);
    tmp30 <@ abi_decode_array_uint256_dyn_calldata(_16, dataEnd);
    (value4,value5) <- tmp30;
    return (value0, value1, value2, value3, value4, value5);
    }
  
  proc usr_evaluateLagrangePolyOutOfDomain(usr_polyNum : uint256, usr_at : uint256): uint256 = {
    var usr_res, usr_omegaPower, _1, tmp266, _2, _3, _4, _5, _6, tmp267, _7, _8, _9, tmp268, _10, usr_denominator, _11, _12, tmp269;
    usr_omegaPower <- (W256.of_int 1);
    if ((bool_of_uint256 usr_polyNum))
      {
      _1 <- (W256.of_int 13446667982376394161563610564587413125564757801019538732601045199901075958935);
      tmp266 <@ usr_modexp(_1, usr_polyNum);
      usr_omegaPower <- tmp266;
      
      }
    
    _2 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _3 <- (W256.of_int 1);
    _4 <- (_2 - _3);
    _5 <- (W256.of_int 67108864);
    tmp267 <@ usr_modexp(usr_at, _5);
    _6 <- tmp267;
    usr_res <- (PurePrimops.addmod _6 _4 _2);
    _7 <- (PurePrimops.iszero usr_res);
    if ((bool_of_uint256 _7))
      {
      _8 <- (W256.of_int STRING (*invalid vanishing polynomial*));
      _9 <- (W256.of_int 28);
      tmp268 <@ usr_revertWithMessage(_9, _8);
      
      }
    
    usr_res <- (PurePrimops.mulmod usr_res usr_omegaPower _2);
    _10 <- (_2 - usr_omegaPower);
    usr_denominator <- (PurePrimops.addmod usr_at _10 _2);
    usr_denominator <- (PurePrimops.mulmod usr_denominator _5 _2);
    _11 <- (W256.of_int 2);
    _12 <- (_2 - _11);
    tmp269 <@ usr_modexp(usr_denominator, _12);
    usr_denominator <- tmp269;
    usr_res <- (PurePrimops.mulmod usr_res usr_denominator _2);
    return usr_res;
    }
  
  proc usr_updateAggregationChallenge(usr_queriesCommitmentPoint : uint256, usr_valueAtZ : uint256, usr_curAggregationChallenge : uint256, usr_curAggregatedOpeningAtZ : uint256): (uint256 * uint256) = {
    var usr_newAggregationChallenge, usr_newAggregatedOpeningAtZ, _1, _2, _3, tmp370, _4, tmp371, _5, tmp372, _6;
    _1 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _2 <- (W256.of_int 4000);
    tmp370 <@ Primops.mload(_2);
    _3 <- tmp370;
    usr_newAggregationChallenge <- (PurePrimops.mulmod usr_curAggregationChallenge _3 _1);
    _4 <- (W256.of_int 4480);
    tmp371 <@ usr_pointMulAndAddIntoDest(usr_queriesCommitmentPoint, usr_newAggregationChallenge, _4);
    tmp372 <@ Primops.mload(usr_valueAtZ);
    _5 <- tmp372;
    _6 <- (PurePrimops.mulmod usr_newAggregationChallenge _5 _1);
    usr_newAggregatedOpeningAtZ <- (PurePrimops.addmod usr_curAggregatedOpeningAtZ _6 _1);
    return (usr_newAggregationChallenge, usr_newAggregatedOpeningAtZ);
    }
  
  proc usr_finalPairing(): unit = {
    var _1, usr_u, tmp412, _2, usr_z, tmp413, _3, _4, _5, tmp414, usr_zOmega, _6, _7, tmp415, _8, tmp416, _9, _10, tmp417, _11, tmp418, _12, _13, _14, tmp419, _15, tmp420, tmp421, _16, _17, tmp422, usr_uu, _18, tmp423, _19, tmp424, _20, tmp425, _21, _22, _23, tmp426, _24, _25, _26, _27, _28, _29, _30, _31, _32, _33, tmp427, _34, _35, tmp428, _36, _37, _38, _39, _40, _41, _42, _43, _44, _45, _46, _47, tmp429, usr_success, tmp430, _48, _49, tmp431, _50, tmp432, _51, _52, _53, tmp433;
    _1 <- (W256.of_int 4032);
    tmp412 <@ Primops.mload(_1);
    usr_u <- tmp412;
    _2 <- (W256.of_int 4064);
    tmp413 <@ Primops.mload(_2);
    usr_z <- tmp413;
    _3 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _4 <- (W256.of_int 13446667982376394161563610564587413125564757801019538732601045199901075958935);
    tmp414 <@ Primops.mload(_2);
    _5 <- tmp414;
    usr_zOmega <- (PurePrimops.mulmod _5 _4 _3);
    _6 <- (W256.of_int 4672);
    _7 <- (W256.of_int 4736);
    tmp415 <@ usr_pointSubAssign(_7, _6);
    _8 <- (W256.of_int 3136);
    tmp416 <@ usr_pointMulAndAddIntoDest(_8, usr_z, _7);
    _9 <- (PurePrimops.mulmod usr_zOmega usr_u _3);
    _10 <- (W256.of_int 3200);
    tmp417 <@ usr_pointMulAndAddIntoDest(_10, _9, _7);
    tmp418 <@ Primops.mload(_8);
    _11 <- tmp418;
    _12 <- (W256.of_int 4864);
    Primops.mstore(_12, _11);
    _13 <- (W256.of_int 3168);
    tmp419 <@ Primops.mload(_13);
    _14 <- tmp419;
    _15 <- (W256.of_int 4896);
    Primops.mstore(_15, _14);
    tmp420 <@ usr_pointMulAndAddIntoDest(_10, usr_u, _12);
    tmp421 <@ usr_pointNegate(_12);
    _16 <- (W256.of_int 1792);
    tmp422 <@ Primops.mload(_16);
    _17 <- tmp422;
    if ((bool_of_uint256 _17))
      {
      usr_uu <- (PurePrimops.mulmod usr_u usr_u _3);
      _18 <- (W256.of_int 3264);
      tmp423 <@ usr_pointMulAndAddIntoDest(_18, usr_uu, _7);
      _19 <- (W256.of_int 3328);
      tmp424 <@ usr_pointMulAndAddIntoDest(_19, usr_uu, _12);
      
      }
    
    tmp425 <@ Primops.mload(_7);
    _20 <- tmp425;
    _21 <- (W256.of_int 0);
    Primops.mstore(_21, _20);
    _22 <- (W256.of_int 4768);
    tmp426 <@ Primops.mload(_22);
    _23 <- tmp426;
    _24 <- (W256.of_int 32);
    Primops.mstore(_24, _23);
    _25 <- (W256.of_int 11559732032986387107991004021392285783925812861821192530917403151452391805634);
    _26 <- (W256.of_int 64);
    Primops.mstore(_26, _25);
    _27 <- (W256.of_int 10857046999023057135944570762232829481370756359578518086990519993285655852781);
    _28 <- (W256.of_int 96);
    Primops.mstore(_28, _27);
    _29 <- (W256.of_int 4082367875863433681332203403145435568316851327593401208105741076214120093531);
    _30 <- (W256.of_int 128);
    Primops.mstore(_30, _29);
    _31 <- (W256.of_int 8495653923123431417604973247489272438418190587263600148770280649306958101930);
    _32 <- (W256.of_int 160);
    Primops.mstore(_32, _31);
    tmp427 <@ Primops.mload(_12);
    _33 <- tmp427;
    _34 <- (W256.of_int 192);
    Primops.mstore(_34, _33);
    tmp428 <@ Primops.mload(_15);
    _35 <- tmp428;
    _36 <- (W256.of_int 224);
    Primops.mstore(_36, _35);
    _37 <- (W256.of_int 17212635814319756364507010169094758005397460366678210664966334781961899574209);
    _38 <- (W256.of_int 256);
    Primops.mstore(_38, _37);
    _39 <- (W256.of_int 496075682290949347282619629729389528669750910289829251317610107342504362928);
    _40 <- (W256.of_int 288);
    Primops.mstore(_40, _39);
    _41 <- (W256.of_int 2255182984359105691812395885056400739448730162863181907784180250290003009508);
    _42 <- (W256.of_int 320);
    Primops.mstore(_42, _41);
    _43 <- (W256.of_int 15828724851114720558251891430452666121603726704878231219287131634746610441813);
    _44 <- (W256.of_int 352);
    Primops.mstore(_44, _43);
    _45 <- (W256.of_int 384);
    _46 <- (W256.of_int 8);
    tmp429 <@ Primops.gas();
    _47 <- tmp429;
    tmp430 <@ Primops.staticcall(_47, _46, _21, _45, _21, _24);
    usr_success <- tmp430;
    _48 <- (PurePrimops.iszero usr_success);
    if ((bool_of_uint256 _48))
      {
      _49 <- (W256.of_int STRING (*finalPairing: precompile failure*));
      tmp431 <@ usr_revertWithMessage(_24, _49);
      
      }
    
    tmp432 <@ Primops.mload(_21);
    _50 <- tmp432;
    _51 <- (PurePrimops.iszero _50);
    if ((bool_of_uint256 _51))
      {
      _52 <- (W256.of_int STRING (*finalPairing: pairing failure*));
      _53 <- (W256.of_int 29);
      tmp433 <@ usr_revertWithMessage(_53, _52);
      
      }
    
    }
  
  proc abi_encode_bool(headStart : uint256, value0 : uint256): uint256 = {
    var tail, _1, _2, _3, tmp32;
    _1 <- (W256.of_int 32);
    tail <- (headStart + _1);
    _2 <- (W256.of_int 0);
    _3 <- (headStart + _2);
    tmp32 <@ abi_encode_bool_to_bool(value0, _3);
    return tail;
    }
  
  proc usr_updateAggregationChallenge_105(usr_queriesCommitmentPoint : uint256, usr_valueAtZ_Omega : uint256, usr_previousCoeff : uint256, usr_curAggregationChallenge : uint256, usr_curAggregatedOpeningAtZ_Omega : uint256): (uint256 * uint256) = {
    var usr_newAggregationChallenge, usr_newAggregatedOpeningAtZ_Omega, _1, _2, _3, tmp373, _4, _5, tmp374, _6, usr_finalCoeff, _7, tmp375, _8, tmp376, _9;
    _1 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _2 <- (W256.of_int 4000);
    tmp373 <@ Primops.mload(_2);
    _3 <- tmp373;
    usr_newAggregationChallenge <- (PurePrimops.mulmod usr_curAggregationChallenge _3 _1);
    _4 <- (W256.of_int 4032);
    tmp374 <@ Primops.mload(_4);
    _5 <- tmp374;
    _6 <- (PurePrimops.mulmod usr_newAggregationChallenge _5 _1);
    usr_finalCoeff <- (PurePrimops.addmod usr_previousCoeff _6 _1);
    _7 <- (W256.of_int 4544);
    tmp375 <@ usr_pointMulAndAddIntoDest(usr_queriesCommitmentPoint, usr_finalCoeff, _7);
    tmp376 <@ Primops.mload(usr_valueAtZ_Omega);
    _8 <- tmp376;
    _9 <- (PurePrimops.mulmod usr_newAggregationChallenge _8 _1);
    usr_newAggregatedOpeningAtZ_Omega <- (PurePrimops.addmod usr_curAggregatedOpeningAtZ_Omega _9 _1);
    return (usr_newAggregationChallenge, usr_newAggregatedOpeningAtZ_Omega);
    }
  
  proc usr_lookupQuotientContribution(): uint256 = {
    var usr_res, _1, usr_betaLookup, tmp283, _2, usr_gammaLookup, tmp284, _3, _4, usr_betaPlusOne, usr_betaGamma, _5, _6, _7, _8, tmp285, _9, _10, tmp286, _11, _12, tmp287, _13, _14, _15, usr_lastOmega, tmp288, _16, _17, _18, tmp289, usr_zMinusLastOmega, _19, _20, _21, tmp290, _22, _23, tmp291, usr_intermediateValue, _24, _25, usr_lnMinusOneAtZ, tmp292, usr_betaGammaPowered, tmp293, _26, usr_alphaPower8, tmp294, _27, usr_subtrahend, _28;
    _1 <- (W256.of_int 3872);
    tmp283 <@ Primops.mload(_1);
    usr_betaLookup <- tmp283;
    _2 <- (W256.of_int 3904);
    tmp284 <@ Primops.mload(_2);
    usr_gammaLookup <- tmp284;
    _3 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _4 <- (W256.of_int 1);
    usr_betaPlusOne <- (PurePrimops.addmod usr_betaLookup _4 _3);
    usr_betaGamma <- (PurePrimops.mulmod usr_betaPlusOne usr_gammaLookup _3);
    _5 <- (W256.of_int 3936);
    Primops.mstore(_5, usr_betaPlusOne);
    _6 <- (W256.of_int 3968);
    Primops.mstore(_6, usr_betaGamma);
    _7 <- (W256.of_int 2880);
    tmp285 <@ Primops.mload(_7);
    _8 <- tmp285;
    usr_res <- (PurePrimops.mulmod _8 usr_betaLookup _3);
    usr_res <- (PurePrimops.addmod usr_res usr_betaGamma _3);
    _9 <- (W256.of_int 2912);
    tmp286 <@ Primops.mload(_9);
    _10 <- tmp286;
    usr_res <- (PurePrimops.mulmod usr_res _10 _3);
    _11 <- (W256.of_int 3744);
    tmp287 <@ Primops.mload(_11);
    _12 <- tmp287;
    usr_res <- (PurePrimops.mulmod usr_res _12 _3);
    _13 <- (W256.of_int 67108864);
    _14 <- (_13 - _4);
    _15 <- (W256.of_int 13446667982376394161563610564587413125564757801019538732601045199901075958935);
    tmp288 <@ usr_modexp(_15, _14);
    usr_lastOmega <- tmp288;
    _16 <- (_3 - usr_lastOmega);
    _17 <- (W256.of_int 4064);
    tmp289 <@ Primops.mload(_17);
    _18 <- tmp289;
    usr_zMinusLastOmega <- (PurePrimops.addmod _18 _16 _3);
    _19 <- (W256.of_int 4096);
    Primops.mstore(_19, usr_zMinusLastOmega);
    usr_res <- (PurePrimops.mulmod usr_res usr_zMinusLastOmega _3);
    _20 <- (W256.of_int 3776);
    tmp290 <@ Primops.mload(_20);
    _21 <- tmp290;
    _22 <- (W256.of_int 4128);
    tmp291 <@ Primops.mload(_22);
    _23 <- tmp291;
    usr_intermediateValue <- (PurePrimops.mulmod _23 _21 _3);
    _24 <- (_3 - usr_intermediateValue);
    usr_res <- (PurePrimops.addmod usr_res _24 _3);
    _25 <- (W256.of_int 4160);
    tmp292 <@ Primops.mload(_25);
    usr_lnMinusOneAtZ <- tmp292;
    tmp293 <@ usr_modexp(usr_betaGamma, _14);
    usr_betaGammaPowered <- tmp293;
    _26 <- (W256.of_int 3808);
    tmp294 <@ Primops.mload(_26);
    usr_alphaPower8 <- tmp294;
    _27 <- (PurePrimops.mulmod usr_lnMinusOneAtZ usr_betaGammaPowered _3);
    usr_subtrahend <- (PurePrimops.mulmod _27 usr_alphaPower8 _3);
    _28 <- (_3 - usr_subtrahend);
    usr_res <- (PurePrimops.addmod usr_res _28 _3);
    return usr_res;
    }
  
  proc usr_mainGateLinearisationContributionWithV(usr_dest : uint256, usr_stateOpening0AtZ : uint256, usr_stateOpening1AtZ : uint256, usr_stateOpening2AtZ : uint256, usr_stateOpening3AtZ : uint256): unit = {
    var _1, tmp295, _2, tmp296, _3, tmp297, _4, tmp298, _5, _6, _7, tmp299, _8, _9, tmp300, _10, tmp301, _11, _12, tmp302, _13, tmp303, _14, _15, tmp304, _16, _17, tmp305, usr_coeff, tmp306;
    _1 <- (W256.of_int 512);
    tmp295 <@ usr_pointMulIntoDest(_1, usr_stateOpening0AtZ, usr_dest);
    _2 <- (W256.of_int 576);
    tmp296 <@ usr_pointMulAndAddIntoDest(_2, usr_stateOpening1AtZ, usr_dest);
    _3 <- (W256.of_int 640);
    tmp297 <@ usr_pointMulAndAddIntoDest(_3, usr_stateOpening2AtZ, usr_dest);
    _4 <- (W256.of_int 704);
    tmp298 <@ usr_pointMulAndAddIntoDest(_4, usr_stateOpening3AtZ, usr_dest);
    _5 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _6 <- (PurePrimops.mulmod usr_stateOpening0AtZ usr_stateOpening1AtZ _5);
    _7 <- (W256.of_int 768);
    tmp299 <@ usr_pointMulAndAddIntoDest(_7, _6, usr_dest);
    _8 <- (PurePrimops.mulmod usr_stateOpening0AtZ usr_stateOpening2AtZ _5);
    _9 <- (W256.of_int 832);
    tmp300 <@ usr_pointMulAndAddIntoDest(_9, _8, usr_dest);
    _10 <- (W256.of_int 896);
    tmp301 <@ usr_pointAddAssign(usr_dest, _10);
    _11 <- (W256.of_int 2688);
    tmp302 <@ Primops.mload(_11);
    _12 <- tmp302;
    _13 <- (W256.of_int 960);
    tmp303 <@ usr_pointMulAndAddIntoDest(_13, _12, usr_dest);
    _14 <- (W256.of_int 4000);
    tmp304 <@ Primops.mload(_14);
    _15 <- tmp304;
    _16 <- (W256.of_int 2720);
    tmp305 <@ Primops.mload(_16);
    _17 <- tmp305;
    usr_coeff <- (PurePrimops.mulmod _17 _15 _5);
    tmp306 <@ usr_pointMulIntoDest(usr_dest, usr_coeff, usr_dest);
    }
  
  proc abi_encode_bytes32(headStart : uint256, value0 : uint256): uint256 = {
    var tail, _1, _2, _3, tmp39;
    _1 <- (W256.of_int 32);
    tail <- (headStart + _1);
    _2 <- (W256.of_int 0);
    _3 <- (headStart + _2);
    tmp39 <@ abi_encode_bytes32_to_bytes32(value0, _3);
    return tail;
    }
  
  proc usr_addAssignRescueCustomGateLinearisationContributionWithV(usr_dest : uint256, usr_stateOpening0AtZ : uint256, usr_stateOpening1AtZ : uint256, usr_stateOpening2AtZ : uint256, usr_stateOpening3AtZ : uint256): unit = {
    var usr_accumulator, usr_intermediateValue, _1, _2, _3, _4, tmp307, _5, _6, _7, tmp308, _8, _9, _10, tmp309, _11, _12, tmp310, _13, tmp311;
    _1 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_accumulator <- (PurePrimops.mulmod usr_stateOpening0AtZ usr_stateOpening0AtZ _1);
    _2 <- (_1 - usr_stateOpening1AtZ);
    usr_accumulator <- (PurePrimops.addmod usr_accumulator _2 _1);
    _3 <- (W256.of_int 3520);
    tmp307 <@ Primops.mload(_3);
    _4 <- tmp307;
    usr_accumulator <- (PurePrimops.mulmod usr_accumulator _4 _1);
    usr_intermediateValue <- (PurePrimops.mulmod usr_stateOpening1AtZ usr_stateOpening1AtZ _1);
    _5 <- (_1 - usr_stateOpening2AtZ);
    usr_intermediateValue <- (PurePrimops.addmod usr_intermediateValue _5 _1);
    _6 <- (W256.of_int 3616);
    tmp308 <@ Primops.mload(_6);
    _7 <- tmp308;
    usr_intermediateValue <- (PurePrimops.mulmod usr_intermediateValue _7 _1);
    usr_accumulator <- (PurePrimops.addmod usr_accumulator usr_intermediateValue _1);
    usr_intermediateValue <- (PurePrimops.mulmod usr_stateOpening2AtZ usr_stateOpening0AtZ _1);
    _8 <- (_1 - usr_stateOpening3AtZ);
    usr_intermediateValue <- (PurePrimops.addmod usr_intermediateValue _8 _1);
    _9 <- (W256.of_int 3648);
    tmp309 <@ Primops.mload(_9);
    _10 <- tmp309;
    usr_intermediateValue <- (PurePrimops.mulmod usr_intermediateValue _10 _1);
    usr_accumulator <- (PurePrimops.addmod usr_accumulator usr_intermediateValue _1);
    _11 <- (W256.of_int 4000);
    tmp310 <@ Primops.mload(_11);
    _12 <- tmp310;
    usr_accumulator <- (PurePrimops.mulmod usr_accumulator _12 _1);
    _13 <- (W256.of_int 1088);
    tmp311 <@ usr_pointMulAndAddIntoDest(_13, usr_accumulator, usr_dest);
    }
  
  (* proc external_fun_verificationKeyHash(): unit = { *)
  (*   var _1, tmp40, tmp41, _2, tmp42, _3, tmp43, ret, tmp44, memPos, tmp45, memEnd, tmp46, _4; *)
  (*   tmp40 <@ callvalue(); *)
  (*   _1 <- tmp40; *)
  (*   if ((bool_of_uint256 _1)) *)
  (*     { *)
  (*     tmp41 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(); *)
      
  (*     } *)
    
  (*   tmp42 <@ Primops.calldatasize(); *)
  (*   _2 <- tmp42; *)
  (*   _3 <- (W256.of_int 4); *)
  (*   tmp43 <@ abi_decode(_3, _2); *)
  (*   tmp44 <@ fun_verificationKeyHash(); *)
  (*   ret <- tmp44; *)
  (*   tmp45 <@ allocate_unbounded(); *)
  (*   memPos <- tmp45; *)
  (*   tmp46 <@ abi_encode_bytes32(memPos, ret); *)
  (*   memEnd <- tmp46; *)
  (*   _4 <- (memEnd - memPos); *)
  (*   Primops.evm_return(memPos, _4); *)
  (*   } *)
  
  proc usr_verifyQuotientEvaluation(): unit = {
    var _1, usr_alpha, tmp253, _2, usr_currentAlpha, _3, _4, _5, _6, _7, _8, _9, _10, usr_stateZ, tmp254, _11, _12, tmp255, _13, _14, _15, _16, _17, tmp256, _18, _19, _20, tmp257, _21, tmp258, usr_stateT, _22, _23, tmp259, usr_result, _24, tmp260, _25, tmp261, _26, _27, tmp262, _28, _29, _30, tmp263, usr_vanishing, _31, _32, tmp264, usr_lhs, _33, _34, _35, _36, tmp265;
    _1 <- (W256.of_int 3520);
    tmp253 <@ Primops.mload(_1);
    usr_alpha <- tmp253;
    _2 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_currentAlpha <- (PurePrimops.mulmod usr_alpha usr_alpha _2);
    _3 <- (W256.of_int 3616);
    Primops.mstore(_3, usr_currentAlpha);
    usr_currentAlpha <- (PurePrimops.mulmod usr_currentAlpha usr_alpha _2);
    _4 <- (W256.of_int 3648);
    Primops.mstore(_4, usr_currentAlpha);
    usr_currentAlpha <- (PurePrimops.mulmod usr_currentAlpha usr_alpha _2);
    _5 <- (W256.of_int 3680);
    Primops.mstore(_5, usr_currentAlpha);
    usr_currentAlpha <- (PurePrimops.mulmod usr_currentAlpha usr_alpha _2);
    _6 <- (W256.of_int 3712);
    Primops.mstore(_6, usr_currentAlpha);
    usr_currentAlpha <- (PurePrimops.mulmod usr_currentAlpha usr_alpha _2);
    _7 <- (W256.of_int 3744);
    Primops.mstore(_7, usr_currentAlpha);
    usr_currentAlpha <- (PurePrimops.mulmod usr_currentAlpha usr_alpha _2);
    _8 <- (W256.of_int 3776);
    Primops.mstore(_8, usr_currentAlpha);
    usr_currentAlpha <- (PurePrimops.mulmod usr_currentAlpha usr_alpha _2);
    _9 <- (W256.of_int 3808);
    Primops.mstore(_9, usr_currentAlpha);
    _10 <- (W256.of_int 4064);
    tmp254 <@ Primops.mload(_10);
    usr_stateZ <- tmp254;
    _11 <- (W256.of_int 0);
    tmp255 <@ usr_evaluateLagrangePolyOutOfDomain(_11, usr_stateZ);
    _12 <- tmp255;
    _13 <- (W256.of_int 4128);
    Primops.mstore(_13, _12);
    _14 <- (W256.of_int 1);
    _15 <- (W256.of_int 67108864);
    _16 <- (_15 - _14);
    tmp256 <@ usr_evaluateLagrangePolyOutOfDomain(_16, usr_stateZ);
    _17 <- tmp256;
    _18 <- (W256.of_int 4160);
    Primops.mstore(_18, _17);
    _19 <- (W256.of_int 1824);
    tmp257 <@ Primops.mload(_19);
    _20 <- tmp257;
    tmp258 <@ Primops.mload(_13);
    _21 <- tmp258;
    usr_stateT <- (PurePrimops.mulmod _21 _20 _2);
    _22 <- (W256.of_int 2720);
    tmp259 <@ Primops.mload(_22);
    _23 <- tmp259;
    usr_result <- (PurePrimops.mulmod usr_stateT _23 _2);
    tmp260 <@ usr_permutationQuotientContribution();
    _24 <- tmp260;
    usr_result <- (PurePrimops.addmod usr_result _24 _2);
    tmp261 <@ usr_lookupQuotientContribution();
    _25 <- tmp261;
    usr_result <- (PurePrimops.addmod usr_result _25 _2);
    _26 <- (W256.of_int 3104);
    tmp262 <@ Primops.mload(_26);
    _27 <- tmp262;
    usr_result <- (PurePrimops.addmod _27 usr_result _2);
    _28 <- (_2 - _14);
    _29 <- (W256.of_int 4192);
    tmp263 <@ Primops.mload(_29);
    _30 <- tmp263;
    usr_vanishing <- (PurePrimops.addmod _30 _28 _2);
    _31 <- (W256.of_int 3072);
    tmp264 <@ Primops.mload(_31);
    _32 <- tmp264;
    usr_lhs <- (PurePrimops.mulmod _32 usr_vanishing _2);
    _33 <- (PurePrimops.eq_uint256 usr_lhs usr_result);
    _34 <- (PurePrimops.iszero _33);
    if ((bool_of_uint256 _34))
      {
      _35 <- (W256.of_int STRING (*invalid quotient evaluation*));
      _36 <- (W256.of_int 27);
      tmp265 <@ usr_revertWithMessage(_36, _35);
      
      }
    
    }
  
  proc usr_prepareQueries(): unit = {
    var _1, usr_zInDomainSize, tmp350, usr_currentZ, _2, _3, tmp351, _4, _5, _6, tmp352, _7, _8, tmp353, _9, _10, tmp354, _11, tmp355, _12, usr_stateOpening0AtZ, tmp356, _13, usr_stateOpening1AtZ, tmp357, _14, usr_stateOpening2AtZ, tmp358, _15, usr_stateOpening3AtZ, tmp359, _16, tmp360, tmp361, tmp362, tmp363, _17, _18, tmp364, _19, _20, _21, tmp365, _22, _23, usr_eta, tmp366, usr_currentEta, _24, tmp367, _25, tmp368, _26, tmp369;
    _1 <- (W256.of_int 4192);
    tmp350 <@ Primops.mload(_1);
    usr_zInDomainSize <- tmp350;
    usr_currentZ <- usr_zInDomainSize;
    _2 <- (W256.of_int 2304);
    tmp351 <@ Primops.mload(_2);
    _3 <- tmp351;
    _4 <- (W256.of_int 4288);
    Primops.mstore(_4, _3);
    _5 <- (W256.of_int 2336);
    tmp352 <@ Primops.mload(_5);
    _6 <- tmp352;
    _7 <- (W256.of_int 4320);
    Primops.mstore(_7, _6);
    _8 <- (W256.of_int 2368);
    tmp353 <@ usr_pointMulAndAddIntoDest(_8, usr_zInDomainSize, _4);
    _9 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_currentZ <- (PurePrimops.mulmod usr_zInDomainSize usr_zInDomainSize _9);
    _10 <- (W256.of_int 2432);
    tmp354 <@ usr_pointMulAndAddIntoDest(_10, usr_currentZ, _4);
    usr_currentZ <- (PurePrimops.mulmod usr_currentZ usr_zInDomainSize _9);
    _11 <- (W256.of_int 2496);
    tmp355 <@ usr_pointMulAndAddIntoDest(_11, usr_currentZ, _4);
    _12 <- (W256.of_int 2560);
    tmp356 <@ Primops.mload(_12);
    usr_stateOpening0AtZ <- tmp356;
    _13 <- (W256.of_int 2592);
    tmp357 <@ Primops.mload(_13);
    usr_stateOpening1AtZ <- tmp357;
    _14 <- (W256.of_int 2624);
    tmp358 <@ Primops.mload(_14);
    usr_stateOpening2AtZ <- tmp358;
    _15 <- (W256.of_int 2656);
    tmp359 <@ Primops.mload(_15);
    usr_stateOpening3AtZ <- tmp359;
    _16 <- (W256.of_int 4352);
    tmp360 <@ usr_mainGateLinearisationContributionWithV(_16, usr_stateOpening0AtZ, usr_stateOpening1AtZ, usr_stateOpening2AtZ, usr_stateOpening3AtZ);
    tmp361 <@ usr_addAssignRescueCustomGateLinearisationContributionWithV(_16, usr_stateOpening0AtZ, usr_stateOpening1AtZ, usr_stateOpening2AtZ, usr_stateOpening3AtZ);
    tmp362 <@ usr_addAssignPermutationLinearisationContributionWithV(_16, usr_stateOpening0AtZ, usr_stateOpening1AtZ, usr_stateOpening2AtZ, usr_stateOpening3AtZ);
    tmp363 <@ usr_addAssignLookupLinearisationContributionWithV(_16, usr_stateOpening0AtZ, usr_stateOpening1AtZ, usr_stateOpening2AtZ);
    _17 <- (W256.of_int 1472);
    tmp364 <@ Primops.mload(_17);
    _18 <- tmp364;
    _19 <- (W256.of_int 4416);
    Primops.mstore(_19, _18);
    _20 <- (W256.of_int 1504);
    tmp365 <@ Primops.mload(_20);
    _21 <- tmp365;
    _22 <- (W256.of_int 4448);
    Primops.mstore(_22, _21);
    _23 <- (W256.of_int 3840);
    tmp366 <@ Primops.mload(_23);
    usr_eta <- tmp366;
    usr_currentEta <- usr_eta;
    _24 <- (W256.of_int 1536);
    tmp367 <@ usr_pointMulAndAddIntoDest(_24, usr_eta, _19);
    usr_currentEta <- (PurePrimops.mulmod usr_eta usr_eta _9);
    _25 <- (W256.of_int 1600);
    tmp368 <@ usr_pointMulAndAddIntoDest(_25, usr_currentEta, _19);
    usr_currentEta <- (PurePrimops.mulmod usr_currentEta usr_eta _9);
    _26 <- (W256.of_int 1664);
    tmp369 <@ usr_pointMulAndAddIntoDest(_26, usr_currentEta, _19);
    }
  
  proc usr_prepareAggregatedCommitment(): unit = {
    var usr_aggregationChallenge, usr_firstDCoeff, usr_firstTCoeff, _1, _2, tmp377, _3, _4, _5, tmp378, _6, _7, usr_aggregatedOpeningAtZ, tmp379, _8, tmp380, _9, _10, _11, tmp381, _12, _13, tmp382, _14, _15, _16, tmp383, _17, _18, tmp384, _19, _20, tmp385, _21, tmp386, _22, _23, tmp387, _24, _25, _26, tmp388, _27, _28, tmp389, _29, _30, tmp390, _31, _32, tmp391, _33, tmp392, _34, _35, tmp393, _36, _37, _38, tmp394, _39, _40, tmp395, _41, _42, tmp396, _43, _44, tmp397, _45, _46, _47, tmp398, usr_copyPermutationCoeff, _48, _49, tmp399, _50, _51, tmp400, usr_aggregatedOpeningAtZOmega, _52, _53, tmp401, _54, _55, tmp402, _56, _57, tmp403, _58, _59, tmp404, _60, _61, tmp405, _62, _63, tmp406, _64, usr_u, tmp407, _65, tmp408, _66, tmp409, _67, tmp410, _68, usr_aggregatedValue, _69, _70, _71, _72, tmp411;
    usr_aggregationChallenge <- (W256.of_int 1);
    _1 <- (W256.of_int 4288);
    tmp377 <@ Primops.mload(_1);
    _2 <- tmp377;
    _3 <- (W256.of_int 4480);
    Primops.mstore(_3, _2);
    _4 <- (W256.of_int 4320);
    tmp378 <@ Primops.mload(_4);
    _5 <- tmp378;
    _6 <- (W256.of_int 4512);
    Primops.mstore(_6, _5);
    _7 <- (W256.of_int 3072);
    tmp379 <@ Primops.mload(_7);
    usr_aggregatedOpeningAtZ <- tmp379;
    _8 <- (W256.of_int 4352);
    tmp380 <@ usr_pointAddIntoDest(_3, _8, _3);
    _9 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _10 <- (W256.of_int 4000);
    tmp381 <@ Primops.mload(_10);
    _11 <- tmp381;
    usr_aggregationChallenge <- (PurePrimops.mulmod usr_aggregationChallenge _11 _9);
    _12 <- (W256.of_int 3104);
    tmp382 <@ Primops.mload(_12);
    _13 <- tmp382;
    _14 <- (PurePrimops.mulmod usr_aggregationChallenge _13 _9);
    usr_aggregatedOpeningAtZ <- (PurePrimops.addmod usr_aggregatedOpeningAtZ _14 _9);
    _15 <- (W256.of_int 2560);
    _16 <- (W256.of_int 1856);
    tmp383 <@ usr_updateAggregationChallenge(_16, _15, usr_aggregationChallenge, usr_aggregatedOpeningAtZ);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZ) <- tmp383;
    _17 <- (W256.of_int 2592);
    _18 <- (W256.of_int 1920);
    tmp384 <@ usr_updateAggregationChallenge(_18, _17, usr_aggregationChallenge, usr_aggregatedOpeningAtZ);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZ) <- tmp384;
    _19 <- (W256.of_int 2624);
    _20 <- (W256.of_int 1984);
    tmp385 <@ usr_updateAggregationChallenge(_20, _19, usr_aggregationChallenge, usr_aggregatedOpeningAtZ);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZ) <- tmp385;
    tmp386 <@ Primops.mload(_10);
    _21 <- tmp386;
    usr_aggregationChallenge <- (PurePrimops.mulmod usr_aggregationChallenge _21 _9);
    usr_firstDCoeff <- usr_aggregationChallenge;
    _22 <- (W256.of_int 2656);
    tmp387 <@ Primops.mload(_22);
    _23 <- tmp387;
    _24 <- (PurePrimops.mulmod usr_aggregationChallenge _23 _9);
    usr_aggregatedOpeningAtZ <- (PurePrimops.addmod usr_aggregatedOpeningAtZ _24 _9);
    _25 <- (W256.of_int 2720);
    _26 <- (W256.of_int 1024);
    tmp388 <@ usr_updateAggregationChallenge(_26, _25, usr_aggregationChallenge, usr_aggregatedOpeningAtZ);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZ) <- tmp388;
    _27 <- (W256.of_int 2752);
    _28 <- (W256.of_int 1152);
    tmp389 <@ usr_updateAggregationChallenge(_28, _27, usr_aggregationChallenge, usr_aggregatedOpeningAtZ);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZ) <- tmp389;
    _29 <- (W256.of_int 2784);
    _30 <- (W256.of_int 1216);
    tmp390 <@ usr_updateAggregationChallenge(_30, _29, usr_aggregationChallenge, usr_aggregatedOpeningAtZ);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZ) <- tmp390;
    _31 <- (W256.of_int 2816);
    _32 <- (W256.of_int 1280);
    tmp391 <@ usr_updateAggregationChallenge(_32, _31, usr_aggregationChallenge, usr_aggregatedOpeningAtZ);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZ) <- tmp391;
    tmp392 <@ Primops.mload(_10);
    _33 <- tmp392;
    usr_aggregationChallenge <- (PurePrimops.mulmod usr_aggregationChallenge _33 _9);
    usr_firstTCoeff <- usr_aggregationChallenge;
    _34 <- (W256.of_int 2944);
    tmp393 <@ Primops.mload(_34);
    _35 <- tmp393;
    _36 <- (PurePrimops.mulmod usr_aggregationChallenge _35 _9);
    usr_aggregatedOpeningAtZ <- (PurePrimops.addmod usr_aggregatedOpeningAtZ _36 _9);
    _37 <- (W256.of_int 3008);
    _38 <- (W256.of_int 1408);
    tmp394 <@ usr_updateAggregationChallenge(_38, _37, usr_aggregationChallenge, usr_aggregatedOpeningAtZ);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZ) <- tmp394;
    _39 <- (W256.of_int 3040);
    _40 <- (W256.of_int 1728);
    tmp395 <@ usr_updateAggregationChallenge(_40, _39, usr_aggregationChallenge, usr_aggregatedOpeningAtZ);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZ) <- tmp395;
    _41 <- (W256.of_int 4608);
    Primops.mstore(_41, usr_aggregatedOpeningAtZ);
    tmp396 <@ Primops.mload(_10);
    _42 <- tmp396;
    usr_aggregationChallenge <- (PurePrimops.mulmod usr_aggregationChallenge _42 _9);
    _43 <- (W256.of_int 4032);
    tmp397 <@ Primops.mload(_43);
    _44 <- tmp397;
    _45 <- (PurePrimops.mulmod usr_aggregationChallenge _44 _9);
    _46 <- (W256.of_int 4928);
    tmp398 <@ Primops.mload(_46);
    _47 <- tmp398;
    usr_copyPermutationCoeff <- (PurePrimops.addmod _47 _45 _9);
    _48 <- (W256.of_int 4544);
    _49 <- (W256.of_int 2112);
    tmp399 <@ usr_pointMulIntoDest(_49, usr_copyPermutationCoeff, _48);
    _50 <- (W256.of_int 2848);
    tmp400 <@ Primops.mload(_50);
    _51 <- tmp400;
    usr_aggregatedOpeningAtZOmega <- (PurePrimops.mulmod _51 usr_aggregationChallenge _9);
    _52 <- (W256.of_int 2688);
    _53 <- (W256.of_int 2048);
    tmp401 <@ usr_updateAggregationChallenge_105(_53, _52, usr_firstDCoeff, usr_aggregationChallenge, usr_aggregatedOpeningAtZOmega);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZOmega) <- tmp401;
    _54 <- (W256.of_int 4992);
    tmp402 <@ Primops.mload(_54);
    _55 <- tmp402;
    _56 <- (W256.of_int 2880);
    _57 <- (W256.of_int 2176);
    tmp403 <@ usr_updateAggregationChallenge_105(_57, _56, _55, usr_aggregationChallenge, usr_aggregatedOpeningAtZOmega);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZOmega) <- tmp403;
    _58 <- (W256.of_int 4960);
    tmp404 <@ Primops.mload(_58);
    _59 <- tmp404;
    _60 <- (W256.of_int 2912);
    _61 <- (W256.of_int 2240);
    tmp405 <@ usr_updateAggregationChallenge_105(_61, _60, _59, usr_aggregationChallenge, usr_aggregatedOpeningAtZOmega);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZOmega) <- tmp405;
    _62 <- (W256.of_int 2976);
    _63 <- (W256.of_int 4416);
    tmp406 <@ usr_updateAggregationChallenge_105(_63, _62, usr_firstTCoeff, usr_aggregationChallenge, usr_aggregatedOpeningAtZOmega);
    (usr_aggregationChallenge,usr_aggregatedOpeningAtZOmega) <- tmp406;
    _64 <- (W256.of_int 4640);
    Primops.mstore(_64, usr_aggregatedOpeningAtZOmega);
    tmp407 <@ Primops.mload(_43);
    usr_u <- tmp407;
    _65 <- (W256.of_int 4736);
    tmp408 <@ usr_pointAddIntoDest(_3, _48, _65);
    tmp409 <@ Primops.mload(_41);
    _66 <- tmp409;
    tmp410 <@ Primops.mload(_64);
    _67 <- tmp410;
    _68 <- (PurePrimops.mulmod _67 usr_u _9);
    usr_aggregatedValue <- (PurePrimops.addmod _68 _66 _9);
    _69 <- (W256.of_int 1);
    _70 <- (W256.of_int 4672);
    Primops.mstore(_70, _69);
    _71 <- (W256.of_int 2);
    _72 <- (W256.of_int 4704);
    Primops.mstore(_72, _71);
    tmp411 <@ usr_pointMulIntoDest(_70, usr_aggregatedValue, _70);
    }
  
  proc fun_verify(var__offset : uint256, var_length : uint256, var_offset : uint256, var__length : uint256, var_1250_offset : uint256, var_1250_length : uint256): uint256 = {
    var _var, zero_bool, tmp434, tmp435, tmp436, tmp437, tmp438, tmp439, tmp440, _1, _2, _3;
    zero_bool <- zero_value_for_split_bool;
    _var <- zero_bool;
    tmp434 <@ fun_loadVerificationKey();
    tmp435 <@ usr_loadProof();
    tmp436 <@ usr_initializeTranscript();
    tmp437 <@ usr_verifyQuotientEvaluation();
    tmp438 <@ usr_prepareQueries();
    tmp439 <@ usr_prepareAggregatedCommitment();
    tmp440 <@ usr_finalPairing();
    _1 <- (W256.of_int 1);
    _2 <- (W256.of_int 0);
    Primops.mstore(_2, _1);
    _3 <- (W256.of_int 32);
    Primops.evm_return(_2, _3);
    return _var;
    }
  
  (* proc external_fun_verify(): unit = { *)
  (*   var _1, tmp33, tmp34, _2, tmp35, _3, param, param_1, param_2, param_3, param_4, param_5, tmp36, tmp37; *)
  (*   tmp33 <@ callvalue(); *)
  (*   _1 <- tmp33; *)
  (*   if ((bool_of_uint256 _1)) *)
  (*     { *)
  (*     tmp34 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(); *)
      
  (*     } *)
    
  (*   tmp35 <@ Primops.calldatasize(); *)
  (*   _2 <- tmp35; *)
  (*   _3 <- (W256.of_int 4); *)
  (*   tmp36 <@ abi_decode_array_uint256_dyn_calldatat_array_uint256_dyn_calldatat_array_uint256_dyn_calldata(_3, _2); *)
  (*   (param,param_1,param_2,param_3,param_4,param_5) <- tmp36; *)
  (*   tmp37 <@ fun_verify(param, param_1, param_2, param_3, param_4, param_5); *)
  (*   } *)
  
  (* proc _BODY(): unit = { *)
  (*   var zero_bool, tmp434, tmp435, tmp436, tmp437, tmp438, tmp439, tmp440, _1, _2, _3; *)
  (*   _1 <- (W256.of_int 128); *)
  (*   _2 <- (W256.of_int 64); *)
  (*   Primops.mstore(_2, _1); *)
  (*   _3 <- (W256.of_int 4); *)
  (*   tmp9 <@ Primops.calldatasize(); *)
  (*   _4 <- tmp9; *)
  (*   _5 <- (lt _4 _3); *)
  (*   _6 <- (PurePrimops.iszero _5); *)
  (*   if ((bool_of_uint256 _6)) *)
  (*     { *)
  (*     _7 <- (W256.of_int 0); *)
  (*     tmp10 <@ Primops.calldataload(_7); *)
  (*     _8 <- tmp10; *)
  (*     tmp11 <@ shift_right_unsigned(_8); *)
  (*     selector <- tmp11; *)
  (*     tmp12 <- selector; *)
  (*     if ((tmp12 = (W256.of_int 2279198755))) *)
  (*       { *)
  (*       tmp13 <@ external_fun_verify(); *)
        
  (*       } *)
      
  (*     else { *)
  (*       if ((tmp12 = (W256.of_int 2659796434))) *)
  (*         { *)
  (*         tmp14 <@ external_fun_verificationKeyHash(); *)
          
  (*         } *)
        
        
  (*       } *)
      
      
  (*     } *)
    
  (*   tmp15 <@ revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74(); *)
  (*   } *)
  
  
  }.
(* End Verifier_1261 *)
