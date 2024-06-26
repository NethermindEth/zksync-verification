require import UInt256 Memory YulPrimops PurePrimops.
(* Begin Verifier_1261 *)
op zero_value_for_split_bool: uint256 = (W256.of_int 0).

op cleanup_bytes32(value : uint256): uint256 = value.

op zero_value_for_split_bytes32: uint256 = (W256.of_int 0).

module Verifier_1261 = {
  proc revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  proc revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  proc constructor_IVerifier(): unit = {
    }
  
  proc allocate_unbounded(): uint256 = {
    var memPtr, _1, tmp16;
    _1 <- (W256.of_int 64);
    tmp16 <@ Primops.mload(_1);
    memPtr <- tmp16;
    return memPtr;
    }
  
  proc revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef(): unit = {
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
  
  proc revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  proc revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(): unit = {
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
  
  proc revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d(): unit = {
    var _1;
    _1 <- (W256.of_int 0);
    Primops.revert(_1, _1);
    }
  
  
  }.
(* End Verifier_1261 *)
