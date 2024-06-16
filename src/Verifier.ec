(* Begin Verifier_1261 *)
op zero_value_for_split_bytes32: uint256 = 0.

op zero_value_for_split_bool: uint256 = 0.

op cleanup_bytes32(value : uint256): uint256 = value.

module Verifier_1261 = {
  proc revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db(): unit = {
    var _1;
    _1 <- 0;
    return ();
    }
  
  proc usr_addAssignPermutationLinearisationContributionWithV(usr_dest : uint256, usr_stateOpening0AtZ : uint256, usr_stateOpening1AtZ : uint256, usr_stateOpening2AtZ : uint256, usr_stateOpening3AtZ : uint256, param_state_memory : mem): mem = {
    var param_state_memory, usr_factor, tmp312, _1, tmp313, _2, _3, tmp314, usr_gamma, tmp315, _4, usr_intermediateValue, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, usr_l0AtZ, tmp316, _15, _16, tmp317, _17, _18, tmp318, _19, _20, tmp319, _21, tmp320, _22, _23, tmp321, usr_beta, tmp322, usr_gamma_1, tmp323, _24, _25, tmp324, _26, _27, usr_intermediateValue_1, _28, _29, tmp325, _30, _31, _32, _33, tmp326, _34, _35, _36, tmp327, _37, _38, tmp328, tmp329;
    tmp312 <@ mload(3680, param_state_memory);
    usr_factor <- tmp312;
    tmp313 <@ mload(3552, param_state_memory);
    _1 <- tmp313;
    _2 <- 4064;
    tmp314 <@ mload(_2, param_state_memory);
    _3 <- tmp314;
    tmp315 <@ mload(3584, param_state_memory);
    usr_gamma <- tmp315;
    _4 <- addmod(mulmod(_3, _1, 21888242871839275222246405745257275088548364400416034343698204186575808495617), usr_gamma, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_intermediateValue <- addmod(_4, usr_stateOpening0AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- mulmod(usr_factor, usr_intermediateValue, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _5 <- 5;
    _6 <- mulmod(mulmod(_3, _1, 21888242871839275222246405745257275088548364400416034343698204186575808495617), _5, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _7 <- addmod(_6, usr_gamma, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_intermediateValue <- addmod(_7, usr_stateOpening1AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- mulmod(usr_factor, usr_intermediateValue, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _8 <- 7;
    _9 <- mulmod(mulmod(_3, _1, 21888242871839275222246405745257275088548364400416034343698204186575808495617), _8, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _10 <- addmod(_9, usr_gamma, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_intermediateValue <- addmod(_10, usr_stateOpening2AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- mulmod(usr_factor, usr_intermediateValue, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _11 <- 10;
    _12 <- mulmod(mulmod(_3, _1, 21888242871839275222246405745257275088548364400416034343698204186575808495617), _11, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _13 <- addmod(_12, usr_gamma, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_intermediateValue <- addmod(_13, usr_stateOpening3AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- mulmod(usr_factor, usr_intermediateValue, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _14 <- 4128;
    tmp316 <@ mload(_14, param_state_memory);
    usr_l0AtZ <- tmp316;
    _15 <- 3712;
    tmp317 <@ mload(_15, param_state_memory);
    _16 <- tmp317;
    _17 <- mulmod(usr_l0AtZ, _16, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- addmod(usr_factor, _17, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    tmp318 <@ mload(4000, param_state_memory);
    _18 <- tmp318;
    usr_factor <- mulmod(usr_factor, _18, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _19 <- 4928;
    param_state_memory <@ mstore(_19, usr_factor, param_state_memory);
    tmp319 <@ mload(3552, param_state_memory);
    _20 <- tmp319;
    tmp320 <@ mload(3680, param_state_memory);
    _21 <- tmp320;
    usr_factor <- mulmod(_21, _20, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _22 <- 2848;
    tmp321 <@ mload(_22, param_state_memory);
    _23 <- tmp321;
    usr_factor <- mulmod(usr_factor, _23, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    tmp322 <@ mload(3552, param_state_memory);
    usr_beta <- tmp322;
    tmp323 <@ mload(3584, param_state_memory);
    usr_gamma_1 <- tmp323;
    _24 <- 2752;
    tmp324 <@ mload(_24, param_state_memory);
    _25 <- tmp324;
    _26 <- mulmod(_25, usr_beta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _27 <- addmod(_26, usr_gamma_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_intermediateValue_1 <- addmod(_27, usr_stateOpening0AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- mulmod(usr_factor, usr_intermediateValue_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _28 <- 2784;
    tmp325 <@ mload(_28, param_state_memory);
    _29 <- tmp325;
    _30 <- mulmod(_29, usr_beta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _31 <- addmod(_30, usr_gamma_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_intermediateValue_1 <- addmod(_31, usr_stateOpening1AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- mulmod(usr_factor, usr_intermediateValue_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _32 <- 2816;
    tmp326 <@ mload(_32, param_state_memory);
    _33 <- tmp326;
    _34 <- mulmod(_33, usr_beta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _35 <- addmod(_34, usr_gamma_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_intermediateValue_1 <- addmod(_35, usr_stateOpening2AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- mulmod(usr_factor, usr_intermediateValue_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    tmp327 <@ mload(4000, param_state_memory);
    _36 <- tmp327;
    usr_factor <- mulmod(usr_factor, _36, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _37 <- 4224;
    _38 <- 1344;
    tmp328,param_state_memory <@ usr_pointMulIntoDest(_38, usr_factor, _37, param_state_memory);
    tmp329,param_state_memory <@ usr_pointSubAssign(usr_dest, _37, param_state_memory);
    return param_state_memory;
    }
  
  proc external_fun_verify(param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp33, tmp34, _2, tmp35, _3, param, param_1, param_2, param_3, param_4, param_5, tmp36, tmp37;
    tmp33 <@ callvalue();
    _1 <- tmp33;
    if (_1)
      {
      tmp34 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb();
      
      }
    
    tmp35 <@ calldatasize();
    _2 <- tmp35;
    _3 <- 4;
    tmp36 <@ abi_decode_array_uint256_dyn_calldatat_array_uint256_dyn_calldatat_array_uint256_dyn_calldata(_3, _2);
    param,param_1,param_2,param_3,param_4,param_5 <- tmp36;
    tmp37,param_state_memory <@ fun_verify(param, param_1, param_2, param_3, param_4, param_5, param_state_memory);
    pop(tmp37);
    return param_state_memory;
    }
  
  proc fun_verify(var__offset : uint256, var_length : uint256, var_offset : uint256, var__length : uint256, var_1250_offset : uint256, var_1250_length : uint256, param_state_memory : mem): (uint256 * mem) = {
    var var, param_state_memory, zero_bool, tmp434, tmp435, tmp436, tmp437, tmp438, tmp439, tmp440, _1, _2, _3;
    zero_bool <- zero_value_for_split_bool;
    var <- zero_bool;
    tmp434,param_state_memory <@ fun_loadVerificationKey(param_state_memory);
    tmp435,param_state_memory <@ usr_loadProof(param_state_memory);
    tmp436,param_state_memory <@ usr_initializeTranscript(param_state_memory);
    tmp437,param_state_memory <@ usr_verifyQuotientEvaluation(param_state_memory);
    tmp438,param_state_memory <@ usr_prepareQueries(param_state_memory);
    tmp439,param_state_memory <@ usr_prepareAggregatedCommitment(param_state_memory);
    tmp440,param_state_memory <@ usr_finalPairing(param_state_memory);
    _1 <- true;
    _2 <- 0;
    param_state_memory <@ mstore(_2, _1, param_state_memory);
    _3 <- 32;
    return (_2, _3);
    return (var, param_state_memory);
    }
  
  proc fun_loadVerificationKey(param_state_memory : mem): mem = {
    var param_state_memory, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21, _22, _23, _24, _25, _26, _27, _28, _29, _30, _31, _32, _33, _34, _35, _36, _37, _38, _39, _40, _41, _42, _43, _44, _45, _46, _47, _48, _49, _50, _51, _52, _53, _54, _55, _56, _57, _58, _59, _60, _61, _62, _63, _64, _65, _66, _67, _68, _69, _70, _71, _72, _73, _74, _75, _76, _77, _78, _79, _80, _81, _82;
    _1 <- 8752182643819278825281358491109311747488397345835400146720638359015287854690;
    _2 <- 512;
    param_state_memory <@ mstore(_2, _1, param_state_memory);
    _3 <- 11702890106774794311109464320829961639285524182517416836480964755620593036625;
    _4 <- 544;
    param_state_memory <@ mstore(_4, _3, param_state_memory);
    _5 <- 20333726085237242816528533108173405517277666887513325731527458638169740323846;
    _6 <- 576;
    param_state_memory <@ mstore(_6, _5, param_state_memory);
    _7 <- 20895759739260899082484353863151962651671811489085862903974918191239970565727;
    _8 <- 608;
    param_state_memory <@ mstore(_8, _7, param_state_memory);
    _9 <- 1568732599965362807326380099663611053862348508639087822144187543479274466412;
    _10 <- 640;
    param_state_memory <@ mstore(_10, _9, param_state_memory);
    _11 <- 5821054758250780059685638301776364871013117602597489359484409980131967326794;
    _12 <- 672;
    param_state_memory <@ mstore(_12, _11, param_state_memory);
    _13 <- 1869564366554527726271945732583360837778279311090061338642468249261166609475;
    _14 <- 704;
    param_state_memory <@ mstore(_14, _13, param_state_memory);
    _15 <- 6787073056745945161826226704190290609825180409911049644428579916838155209697;
    _16 <- 736;
    param_state_memory <@ mstore(_16, _15, param_state_memory);
    _17 <- 457576930265342335264945522969406804501107665328727087867171094316559181535;
    _18 <- 768;
    param_state_memory <@ mstore(_18, _17, param_state_memory);
    _19 <- 15424863073888926344027107060444259361026863904290125685775015743583967752523;
    _20 <- 800;
    param_state_memory <@ mstore(_20, _19, param_state_memory);
    _21 <- 17470132079837949645292768946901897910488674334073656384858846314172720305794;
    _22 <- 832;
    param_state_memory <@ mstore(_22, _21, param_state_memory);
    _23 <- 545412623592733862227844066395948813122937527333953380716629283051527996076;
    _24 <- 864;
    param_state_memory <@ mstore(_24, _23, param_state_memory);
    _25 <- 3542620684081214281078362979824071457719243923292217179618867142734017714197;
    _26 <- 896;
    param_state_memory <@ mstore(_26, _25, param_state_memory);
    _27 <- 10380438707000372753007289103897630883671902212004026295360039945231108187502;
    _28 <- 928;
    param_state_memory <@ mstore(_28, _27, param_state_memory);
    _29 <- 13086775255118926036233880981068687796723800497694631087151014741591951564618;
    _30 <- 960;
    param_state_memory <@ mstore(_30, _29, param_state_memory);
    _31 <- 97194583370920108185062801930585216368005987855712538133473341181290744675;
    _32 <- 992;
    param_state_memory <@ mstore(_32, _31, param_state_memory);
    _33 <- 11090534100914016361232447120294745393211436081860550365760620284449885924457;
    _34 <- 1024;
    param_state_memory <@ mstore(_34, _33, param_state_memory);
    _35 <- 6190121082107679677011313308624936965782748053078710395209485205617091614781;
    _36 <- 1056;
    param_state_memory <@ mstore(_36, _35, param_state_memory);
    _37 <- 15086136319636422536776088427553286399949509263897119922379735045147898875009;
    _38 <- 1088;
    param_state_memory <@ mstore(_38, _37, param_state_memory);
    _39 <- 14330561162787072568797012175184761164763459595199124517037991495673925464785;
    _40 <- 1120;
    param_state_memory <@ mstore(_40, _39, param_state_memory);
    _41 <- 21323538885080684424185174689480993185750201390966223018512354418490677522148;
    _42 <- 1152;
    param_state_memory <@ mstore(_42, _41, param_state_memory);
    _43 <- 13825385863192118646834397710139923872086647553258488355179808994788744210563;
    _44 <- 1184;
    param_state_memory <@ mstore(_44, _43, param_state_memory);
    _45 <- 8390759602848414205412884900126185284679301543388803089358900543850868129488;
    _46 <- 1216;
    param_state_memory <@ mstore(_46, _45, param_state_memory);
    _47 <- 7069161667387011886642940009688789554068768218554020114127791736575843662652;
    _48 <- 1248;
    param_state_memory <@ mstore(_48, _47, param_state_memory);
    _49 <- 21779692208264067614279093821878517213862501879831804234566704419708093761485;
    _50 <- 1280;
    param_state_memory <@ mstore(_50, _49, param_state_memory);
    _51 <- 14513193766097634962386283396255157053671281137962954471134782133605379519908;
    _52 <- 1312;
    param_state_memory <@ mstore(_52, _51, param_state_memory);
    _53 <- 4751267043421347170875860608378639586591867931662910797110300384786346064625;
    _54 <- 1344;
    param_state_memory <@ mstore(_54, _53, param_state_memory);
    _55 <- 11385717438670984215358012358002661303410243223751533068904005282628107986385;
    _56 <- 1376;
    param_state_memory <@ mstore(_56, _55, param_state_memory);
    _57 <- 20045313662746578028950791395157660351198208045597010788369662325700141348443;
    _58 <- 1472;
    param_state_memory <@ mstore(_58, _57, param_state_memory);
    _59 <- 2200761695078532224145807378118591946349840073460005094399078719163643466856;
    _60 <- 1504;
    param_state_memory <@ mstore(_60, _59, param_state_memory);
    _61 <- 13866646217607640441607041956684111087071997201218815349460750486791109380780;
    _62 <- 1536;
    param_state_memory <@ mstore(_62, _61, param_state_memory);
    _63 <- 13178446611795019678701878053235714968797421377761816259103804833273256298333;
    _64 <- 1568;
    param_state_memory <@ mstore(_64, _63, param_state_memory);
    _65 <- 5057503605752869531452842486824745179648819794307492731589448195268672785801;
    _66 <- 1600;
    param_state_memory <@ mstore(_66, _65, param_state_memory);
    _67 <- 8597434312520299647191152876265164941580478223412397470356037586993894367875;
    _68 <- 1632;
    param_state_memory <@ mstore(_68, _67, param_state_memory);
    _69 <- 1342318055425277544055386589364579054544440640110901993487861472578322387903;
    _70 <- 1664;
    param_state_memory <@ mstore(_70, _69, param_state_memory);
    _71 <- 4438354282468267034382897187461199764068502038746983055473062465446039509158;
    _72 <- 1696;
    param_state_memory <@ mstore(_72, _71, param_state_memory);
    _73 <- 21714794642552531775933093644480516421064284615960245486122726724547638127878;
    _74 <- 1408;
    param_state_memory <@ mstore(_74, _73, param_state_memory);
    _75 <- 20374981665942106195451736226451722737514281476778224282304648903722926579601;
    _76 <- 1440;
    param_state_memory <@ mstore(_76, _75, param_state_memory);
    _77 <- 196778531949039689886328474582670216324308721975620885373710029662715787742;
    _78 <- 1728;
    param_state_memory <@ mstore(_78, _77, param_state_memory);
    _79 <- 11005776646725047106517461026899305486268481542412200771754169232553006481646;
    _80 <- 1760;
    param_state_memory <@ mstore(_80, _79, param_state_memory);
    _81 <- 0;
    _82 <- 1792;
    param_state_memory <@ mstore(_82, _81, param_state_memory);
    return param_state_memory;
    }
  
  proc usr_pointMulIntoDest(usr_point : uint256, usr_s : uint256, usr_dest : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp53, _2, _3, _4, _5, tmp54, _6, _7, _8, _9, tmp55, _10, tmp56, _11, _12, _13, tmp57;
    tmp53 <@ mload(usr_point, param_state_memory);
    _1 <- tmp53;
    _2 <- 0;
    param_state_memory <@ mstore(_2, _1, param_state_memory);
    _3 <- 32;
    _4 <- usr_point + _3;
    tmp54 <@ mload(_4, param_state_memory);
    _5 <- tmp54;
    param_state_memory <@ mstore(_3, _5, param_state_memory);
    _6 <- 64;
    param_state_memory <@ mstore(_6, usr_s, param_state_memory);
    _7 <- 96;
    _8 <- 7;
    tmp55 <@ gas();
    _9 <- tmp55;
    tmp56,param_state_memory <@ staticcall(_9, _8, _2, _7, usr_dest, _6, param_state_memory);
    _10 <- tmp56;
    _11 <- iszero(_10);
    if (_11)
      {
      _12 <- "pointMulIntoDest: ecMul failed";
      _13 <- 30;
      tmp57,param_state_memory <@ usr_revertWithMessage(_13, _12, param_state_memory);
      
      }
    
    return param_state_memory;
    }
  
  proc usr_addAssignLookupLinearisationContributionWithV(usr_dest : uint256, usr_stateOpening0AtZ : uint256, usr_stateOpening1AtZ : uint256, usr_stateOpening2AtZ : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, usr_factor, tmp330, _2, tmp331, _3, tmp332, _4, _5, tmp333, _6, _7, tmp334, _8, _9, tmp335, _10, _11, tmp336, _12, _13, tmp337, usr_fReconstructed, _14, usr_eta, tmp338, usr_currentEta, _15, _16, _17, _18, tmp339, _19, _20, _21, tmp340, _22, _23, tmp341, _24, _25, tmp342, _26, tmp343, _27, tmp344, _28, _29, tmp345, _30, _31, tmp346, _32, _33, _34, tmp347, _35, _36, tmp348, _37, _38, tmp349, _39;
    _1 <- 2912;
    tmp330 <@ mload(_1, param_state_memory);
    usr_factor <- tmp330;
    tmp331 <@ mload(3744, param_state_memory);
    _2 <- tmp331;
    usr_factor <- mulmod(usr_factor, _2, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    tmp332 <@ mload(4096, param_state_memory);
    _3 <- tmp332;
    usr_factor <- mulmod(usr_factor, _3, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _4 <- 4000;
    tmp333 <@ mload(_4, param_state_memory);
    _5 <- tmp333;
    usr_factor <- mulmod(usr_factor, _5, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _6 <- 4992;
    param_state_memory <@ mstore(_6, usr_factor, param_state_memory);
    _7 <- 2976;
    tmp334 <@ mload(_7, param_state_memory);
    usr_factor <- tmp334;
    _8 <- 3872;
    tmp335 <@ mload(_8, param_state_memory);
    _9 <- tmp335;
    usr_factor <- mulmod(usr_factor, _9, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _10 <- 2944;
    tmp336 <@ mload(_10, param_state_memory);
    _11 <- tmp336;
    usr_factor <- addmod(usr_factor, _11, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _12 <- 3968;
    tmp337 <@ mload(_12, param_state_memory);
    _13 <- tmp337;
    usr_factor <- addmod(usr_factor, _13, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_fReconstructed <- usr_stateOpening0AtZ;
    _14 <- 3840;
    tmp338 <@ mload(_14, param_state_memory);
    usr_eta <- tmp338;
    usr_currentEta <- usr_eta;
    _15 <- mulmod(usr_eta, usr_stateOpening1AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_fReconstructed <- addmod(usr_stateOpening0AtZ, _15, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_currentEta <- mulmod(usr_eta, usr_eta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _16 <- mulmod(usr_currentEta, usr_stateOpening2AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_fReconstructed <- addmod(usr_fReconstructed, _16, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_currentEta <- mulmod(usr_currentEta, usr_eta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _17 <- 3040;
    tmp339 <@ mload(_17, param_state_memory);
    _18 <- tmp339;
    _19 <- mulmod(_18, usr_currentEta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_fReconstructed <- addmod(usr_fReconstructed, _19, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _20 <- 3008;
    tmp340 <@ mload(_20, param_state_memory);
    _21 <- tmp340;
    usr_fReconstructed <- mulmod(usr_fReconstructed, _21, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _22 <- 3904;
    tmp341 <@ mload(_22, param_state_memory);
    _23 <- tmp341;
    usr_fReconstructed <- addmod(usr_fReconstructed, _23, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- mulmod(usr_factor, usr_fReconstructed, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _24 <- 3936;
    tmp342 <@ mload(_24, param_state_memory);
    _25 <- tmp342;
    usr_factor <- mulmod(usr_factor, _25, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- 21888242871839275222246405745257275088548364400416034343698204186575808495617 - usr_factor;
    tmp343 <@ mload(3744, param_state_memory);
    _26 <- tmp343;
    usr_factor <- mulmod(usr_factor, _26, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    tmp344 <@ mload(4096, param_state_memory);
    _27 <- tmp344;
    usr_factor <- mulmod(usr_factor, _27, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _28 <- 3776;
    tmp345 <@ mload(_28, param_state_memory);
    _29 <- tmp345;
    _30 <- 4128;
    tmp346 <@ mload(_30, param_state_memory);
    _31 <- tmp346;
    _32 <- mulmod(_31, _29, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- addmod(usr_factor, _32, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _33 <- 3808;
    tmp347 <@ mload(_33, param_state_memory);
    _34 <- tmp347;
    _35 <- 4160;
    tmp348 <@ mload(_35, param_state_memory);
    _36 <- tmp348;
    _37 <- mulmod(_36, _34, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    usr_factor <- addmod(usr_factor, _37, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    tmp349 <@ mload(_4, param_state_memory);
    _38 <- tmp349;
    usr_factor <- mulmod(usr_factor, _38, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _39 <- 4960;
    param_state_memory <@ mstore(_39, usr_factor, param_state_memory);
    return param_state_memory;
    }
  
  proc abi_decode_array_uint256_dyn_calldatat_array_uint256_dyn_calldatat_array_uint256_dyn_calldata(headStart : uint256, dataEnd : uint256): (uint256 * uint256 * uint256 * uint256 * uint256 * uint256) = {
    var value0, value1, value2, value3, value4, value5, _1, _2, _3, tmp21, _4, _5, offset, tmp22, _6, _7, tmp23, _8, tmp24, _9, _10, offset_1, tmp25, _11, tmp26, _12, tmp27, _13, _14, offset_2, tmp28, _15, tmp29, _16, tmp30;
    _1 <- 96;
    _2 <- dataEnd - headStart;
    _3 <- slt(_2, _1);
    if (_3)
      {
      tmp21 <@ revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b();
      
      }
    
    _4 <- 0;
    _5 <- headStart + _4;
    tmp22 <@ calldataload(_5);
    offset <- tmp22;
    _6 <- 18446744073709551615;
    _7 <- gt(offset, _6);
    if (_7)
      {
      tmp23 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
      
      }
    
    _8 <- headStart + offset;
    tmp24 <@ abi_decode_array_uint256_dyn_calldata(_8, dataEnd);
    value0,value1 <- tmp24;
    _9 <- 32;
    _10 <- headStart + _9;
    tmp25 <@ calldataload(_10);
    offset_1 <- tmp25;
    _11 <- gt(offset_1, _6);
    if (_11)
      {
      tmp26 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
      
      }
    
    _12 <- headStart + offset_1;
    tmp27 <@ abi_decode_array_uint256_dyn_calldata(_12, dataEnd);
    value2,value3 <- tmp27;
    _13 <- 64;
    _14 <- headStart + _13;
    tmp28 <@ calldataload(_14);
    offset_2 <- tmp28;
    _15 <- gt(offset_2, _6);
    if (_15)
      {
      tmp29 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
      
      }
    
    _16 <- headStart + offset_2;
    tmp30 <@ abi_decode_array_uint256_dyn_calldata(_16, dataEnd);
    value4,value5 <- tmp30;
    return (value0, value1, value2, value3, value4, value5);
    }
  
  proc allocate_unbounded(param_state_memory : mem): uint256 = {
    var memPtr, _1, tmp16;
    _1 <- 64;
    tmp16 <@ mload(_1, param_state_memory);
    memPtr <- tmp16;
    return memPtr;
    }
  
  proc usr_lookupQuotientContribution(param_state_memory : mem): (uint256 * mem) = {
    var usr_res, param_state_memory, _1, usr_betaLookup, tmp283, _2, usr_gammaLookup, tmp284, _3, _4, usr_betaPlusOne, usr_betaGamma, _5, _6, _7, _8, tmp285, _9, _10, tmp286, _11, _12, tmp287, _13, _14, _15, usr_lastOmega, tmp288, _16, _17, _18, tmp289, usr_zMinusLastOmega, _19, _20, _21, tmp290, _22, _23, tmp291, usr_intermediateValue, _24, _25, usr_lnMinusOneAtZ, tmp292, usr_betaGammaPowered, tmp293, _26, usr_alphaPower8, tmp294, _27, usr_subtrahend, _28;
    _1 <- 3872;
    tmp283 <@ mload(_1, param_state_memory);
    usr_betaLookup <- tmp283;
    _2 <- 3904;
    tmp284 <@ mload(_2, param_state_memory);
    usr_gammaLookup <- tmp284;
    _3 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    _4 <- 1;
    usr_betaPlusOne <- addmod(usr_betaLookup, _4, _3);
    usr_betaGamma <- mulmod(usr_betaPlusOne, usr_gammaLookup, _3);
    _5 <- 3936;
    param_state_memory <@ mstore(_5, usr_betaPlusOne, param_state_memory);
    _6 <- 3968;
    param_state_memory <@ mstore(_6, usr_betaGamma, param_state_memory);
    _7 <- 2880;
    tmp285 <@ mload(_7, param_state_memory);
    _8 <- tmp285;
    usr_res <- mulmod(_8, usr_betaLookup, _3);
    usr_res <- addmod(usr_res, usr_betaGamma, _3);
    _9 <- 2912;
    tmp286 <@ mload(_9, param_state_memory);
    _10 <- tmp286;
    usr_res <- mulmod(usr_res, _10, _3);
    _11 <- 3744;
    tmp287 <@ mload(_11, param_state_memory);
    _12 <- tmp287;
    usr_res <- mulmod(usr_res, _12, _3);
    _13 <- 67108864;
    _14 <- _13 - _4;
    _15 <- 13446667982376394161563610564587413125564757801019538732601045199901075958935;
    tmp288,param_state_memory <@ usr_modexp(_15, _14, param_state_memory);
    usr_lastOmega <- tmp288;
    _16 <- _3 - usr_lastOmega;
    _17 <- 4064;
    tmp289 <@ mload(_17, param_state_memory);
    _18 <- tmp289;
    usr_zMinusLastOmega <- addmod(_18, _16, _3);
    _19 <- 4096;
    param_state_memory <@ mstore(_19, usr_zMinusLastOmega, param_state_memory);
    usr_res <- mulmod(usr_res, usr_zMinusLastOmega, _3);
    _20 <- 3776;
    tmp290 <@ mload(_20, param_state_memory);
    _21 <- tmp290;
    _22 <- 4128;
    tmp291 <@ mload(_22, param_state_memory);
    _23 <- tmp291;
    usr_intermediateValue <- mulmod(_23, _21, _3);
    _24 <- _3 - usr_intermediateValue;
    usr_res <- addmod(usr_res, _24, _3);
    _25 <- 4160;
    tmp292 <@ mload(_25, param_state_memory);
    usr_lnMinusOneAtZ <- tmp292;
    tmp293,param_state_memory <@ usr_modexp(usr_betaGamma, _14, param_state_memory);
    usr_betaGammaPowered <- tmp293;
    _26 <- 3808;
    tmp294 <@ mload(_26, param_state_memory);
    usr_alphaPower8 <- tmp294;
    _27 <- mulmod(usr_lnMinusOneAtZ, usr_betaGammaPowered, _3);
    usr_subtrahend <- mulmod(_27, usr_alphaPower8, _3);
    _28 <- _3 - usr_subtrahend;
    usr_res <- addmod(usr_res, _28, _3);
    return (usr_res, param_state_memory);
    }
  
  proc usr_updateAggregationChallenge(usr_queriesCommitmentPoint : uint256, usr_valueAtZ : uint256, usr_curAggregationChallenge : uint256, usr_curAggregatedOpeningAtZ : uint256, param_state_memory : mem): (uint256 * uint256 * mem) = {
    var usr_newAggregationChallenge, usr_newAggregatedOpeningAtZ, param_state_memory, _1, _2, _3, tmp370, _4, tmp371, _5, tmp372, _6;
    _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    _2 <- 4000;
    tmp370 <@ mload(_2, param_state_memory);
    _3 <- tmp370;
    usr_newAggregationChallenge <- mulmod(usr_curAggregationChallenge, _3, _1);
    _4 <- 4480;
    tmp371,param_state_memory <@ usr_pointMulAndAddIntoDest(usr_queriesCommitmentPoint, usr_newAggregationChallenge, _4, param_state_memory);
    tmp372 <@ mload(usr_valueAtZ, param_state_memory);
    _5 <- tmp372;
    _6 <- mulmod(usr_newAggregationChallenge, _5, _1);
    usr_newAggregatedOpeningAtZ <- addmod(usr_curAggregatedOpeningAtZ, _6, _1);
    return (usr_newAggregationChallenge, usr_newAggregatedOpeningAtZ, param_state_memory);
    }
  
  proc constructor_Verifier(): unit = {
    var tmp8;
    tmp8 <@ constructor_IVerifier();
    }
  
  proc usr_pointMulAndAddIntoDest(usr_point : uint256, usr_s : uint256, usr_dest : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp79, _2, _3, _4, _5, tmp80, _6, _7, _8, _9, tmp81, usr_success, tmp82, _10, tmp83, _11, _12, tmp84, _13, _14, _15, tmp85, _16, tmp86, _17, _18, _19, tmp87;
    tmp79 <@ mload(usr_point, param_state_memory);
    _1 <- tmp79;
    _2 <- 0;
    param_state_memory <@ mstore(_2, _1, param_state_memory);
    _3 <- 32;
    _4 <- usr_point + _3;
    tmp80 <@ mload(_4, param_state_memory);
    _5 <- tmp80;
    param_state_memory <@ mstore(_3, _5, param_state_memory);
    _6 <- 64;
    param_state_memory <@ mstore(_6, usr_s, param_state_memory);
    _7 <- 96;
    _8 <- 7;
    tmp81 <@ gas();
    _9 <- tmp81;
    tmp82,param_state_memory <@ staticcall(_9, _8, _2, _7, _2, _6, param_state_memory);
    usr_success <- tmp82;
    tmp83 <@ mload(usr_dest, param_state_memory);
    _10 <- tmp83;
    param_state_memory <@ mstore(_6, _10, param_state_memory);
    _11 <- usr_dest + _3;
    tmp84 <@ mload(_11, param_state_memory);
    _12 <- tmp84;
    param_state_memory <@ mstore(_7, _12, param_state_memory);
    _13 <- 128;
    _14 <- 6;
    tmp85 <@ gas();
    _15 <- tmp85;
    tmp86,param_state_memory <@ staticcall(_15, _14, _2, _13, usr_dest, _6, param_state_memory);
    _16 <- tmp86;
    usr_success <- usr_success /\ _16;
    _17 <- iszero(usr_success);
    if (_17)
      {
      _18 <- "pointMulAndAddIntoDest";
      _19 <- 22;
      tmp87,param_state_memory <@ usr_revertWithMessage(_19, _18, param_state_memory);
      
      }
    
    return param_state_memory;
    }
  
  proc usr_modexp(usr_value : uint256, usr_power : uint256, param_state_memory : mem): (uint256 * mem) = {
    var usr_res, param_state_memory, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, tmp49, _11, tmp50, _12, _13, _14, tmp51, tmp52;
    _1 <- 32;
    _2 <- 0;
    param_state_memory <@ mstore(_2, _1, param_state_memory);
    param_state_memory <@ mstore(_1, _1, param_state_memory);
    _3 <- 64;
    param_state_memory <@ mstore(_3, _1, param_state_memory);
    _4 <- 96;
    param_state_memory <@ mstore(_4, usr_value, param_state_memory);
    _5 <- 128;
    param_state_memory <@ mstore(_5, usr_power, param_state_memory);
    _6 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    _7 <- 160;
    param_state_memory <@ mstore(_7, _6, param_state_memory);
    _8 <- 192;
    _9 <- 5;
    tmp49 <@ gas();
    _10 <- tmp49;
    tmp50,param_state_memory <@ staticcall(_10, _9, _2, _8, _2, _1, param_state_memory);
    _11 <- tmp50;
    _12 <- iszero(_11);
    if (_12)
      {
      _13 <- "modexp precompile failed";
      _14 <- 24;
      tmp51,param_state_memory <@ usr_revertWithMessage(_14, _13, param_state_memory);
      
      }
    
    tmp52 <@ mload(_2, param_state_memory);
    usr_res <- tmp52;
    return (usr_res, param_state_memory);
    }
  
  proc usr_finalPairing(param_state_memory : mem): mem = {
    var param_state_memory, _1, usr_u, tmp412, _2, usr_z, tmp413, _3, _4, _5, tmp414, usr_zOmega, _6, _7, tmp415, _8, tmp416, _9, _10, tmp417, _11, tmp418, _12, _13, _14, tmp419, _15, tmp420, tmp421, _16, _17, tmp422, usr_uu, _18, tmp423, _19, tmp424, _20, tmp425, _21, _22, _23, tmp426, _24, _25, _26, _27, _28, _29, _30, _31, _32, _33, tmp427, _34, _35, tmp428, _36, _37, _38, _39, _40, _41, _42, _43, _44, _45, _46, _47, tmp429, usr_success, tmp430, _48, _49, tmp431, _50, tmp432, _51, _52, _53, tmp433;
    _1 <- 4032;
    tmp412 <@ mload(_1, param_state_memory);
    usr_u <- tmp412;
    _2 <- 4064;
    tmp413 <@ mload(_2, param_state_memory);
    usr_z <- tmp413;
    _3 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    _4 <- 13446667982376394161563610564587413125564757801019538732601045199901075958935;
    tmp414 <@ mload(_2, param_state_memory);
    _5 <- tmp414;
    usr_zOmega <- mulmod(_5, _4, _3);
    _6 <- 4672;
    _7 <- 4736;
    tmp415,param_state_memory <@ usr_pointSubAssign(_7, _6, param_state_memory);
    _8 <- 3136;
    tmp416,param_state_memory <@ usr_pointMulAndAddIntoDest(_8, usr_z, _7, param_state_memory);
    _9 <- mulmod(usr_zOmega, usr_u, _3);
    _10 <- 3200;
    tmp417,param_state_memory <@ usr_pointMulAndAddIntoDest(_10, _9, _7, param_state_memory);
    tmp418 <@ mload(_8, param_state_memory);
    _11 <- tmp418;
    _12 <- 4864;
    param_state_memory <@ mstore(_12, _11, param_state_memory);
    _13 <- 3168;
    tmp419 <@ mload(_13, param_state_memory);
    _14 <- tmp419;
    _15 <- 4896;
    param_state_memory <@ mstore(_15, _14, param_state_memory);
    tmp420,param_state_memory <@ usr_pointMulAndAddIntoDest(_10, usr_u, _12, param_state_memory);
    tmp421,param_state_memory <@ usr_pointNegate(_12, param_state_memory);
    _16 <- 1792;
    tmp422 <@ mload(_16, param_state_memory);
    _17 <- tmp422;
    if (_17)
      {
      usr_uu <- mulmod(usr_u, usr_u, _3);
      _18 <- 3264;
      tmp423,param_state_memory <@ usr_pointMulAndAddIntoDest(_18, usr_uu, _7, param_state_memory);
      _19 <- 3328;
      tmp424,param_state_memory <@ usr_pointMulAndAddIntoDest(_19, usr_uu, _12, param_state_memory);
      
      }
    
    tmp425 <@ mload(_7, param_state_memory);
    _20 <- tmp425;
    _21 <- 0;
    param_state_memory <@ mstore(_21, _20, param_state_memory);
    _22 <- 4768;
    tmp426 <@ mload(_22, param_state_memory);
    _23 <- tmp426;
    _24 <- 32;
    param_state_memory <@ mstore(_24, _23, param_state_memory);
    _25 <- 11559732032986387107991004021392285783925812861821192530917403151452391805634;
    _26 <- 64;
    param_state_memory <@ mstore(_26, _25, param_state_memory);
    _27 <- 10857046999023057135944570762232829481370756359578518086990519993285655852781;
    _28 <- 96;
    param_state_memory <@ mstore(_28, _27, param_state_memory);
    _29 <- 4082367875863433681332203403145435568316851327593401208105741076214120093531;
    _30 <- 128;
    param_state_memory <@ mstore(_30, _29, param_state_memory);
    _31 <- 8495653923123431417604973247489272438418190587263600148770280649306958101930;
    _32 <- 160;
    param_state_memory <@ mstore(_32, _31, param_state_memory);
    tmp427 <@ mload(_12, param_state_memory);
    _33 <- tmp427;
    _34 <- 192;
    param_state_memory <@ mstore(_34, _33, param_state_memory);
    tmp428 <@ mload(_15, param_state_memory);
    _35 <- tmp428;
    _36 <- 224;
    param_state_memory <@ mstore(_36, _35, param_state_memory);
    _37 <- 17212635814319756364507010169094758005397460366678210664966334781961899574209;
    _38 <- 256;
    param_state_memory <@ mstore(_38, _37, param_state_memory);
    _39 <- 496075682290949347282619629729389528669750910289829251317610107342504362928;
    _40 <- 288;
    param_state_memory <@ mstore(_40, _39, param_state_memory);
    _41 <- 2255182984359105691812395885056400739448730162863181907784180250290003009508;
    _42 <- 320;
    param_state_memory <@ mstore(_42, _41, param_state_memory);
    _43 <- 15828724851114720558251891430452666121603726704878231219287131634746610441813;
    _44 <- 352;
    param_state_memory <@ mstore(_44, _43, param_state_memory);
    _45 <- 384;
    _46 <- 8;
    tmp429 <@ gas();
    _47 <- tmp429;
    tmp430,param_state_memory <@ staticcall(_47, _46, _21, _45, _21, _24, param_state_memory);
    usr_success <- tmp430;
    _48 <- iszero(usr_success);
    if (_48)
      {
      _49 <- "finalPairing: precompile failure";
      tmp431,param_state_memory <@ usr_revertWithMessage(_24, _49, param_state_memory);
      
      }
    
    tmp432 <@ mload(_21, param_state_memory);
    _50 <- tmp432;
    _51 <- iszero(_50);
    if (_51)
      {
      _52 <- "finalPairing: pairing failure";
      _53 <- 29;
      tmp433,param_state_memory <@ usr_revertWithMessage(_53, _52, param_state_memory);
      
      }
    
    return param_state_memory;
    }
  
  proc usr_permutationQuotientContribution(param_state_memory : mem): uint256 = {
    var usr_res, _1, _2, _3, tmp270, _4, _5, tmp271, _6, usr_gamma, tmp272, _7, usr_beta, tmp273, usr_factorMultiplier, _8, _9, tmp274, _10, _11, tmp275, _12, _13, tmp276, _14, _15, tmp277, _16, _17, tmp278, _18, _19, tmp279, _20, _21, tmp280, _22, _23, usr_l0AtZ, tmp281, _24, _25, tmp282, _26;
    _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    _2 <- 2848;
    tmp270 <@ mload(_2, param_state_memory);
    _3 <- tmp270;
    _4 <- 3680;
    tmp271 <@ mload(_4, param_state_memory);
    _5 <- tmp271;
    usr_res <- mulmod(_5, _3, _1);
    _6 <- 3584;
    tmp272 <@ mload(_6, param_state_memory);
    usr_gamma <- tmp272;
    _7 <- 3552;
    tmp273 <@ mload(_7, param_state_memory);
    usr_beta <- tmp273;
    _8 <- 2752;
    tmp274 <@ mload(_8, param_state_memory);
    _9 <- tmp274;
    usr_factorMultiplier <- mulmod(_9, usr_beta, _1);
    usr_factorMultiplier <- addmod(usr_factorMultiplier, usr_gamma, _1);
    _10 <- 2560;
    tmp275 <@ mload(_10, param_state_memory);
    _11 <- tmp275;
    usr_factorMultiplier <- addmod(usr_factorMultiplier, _11, _1);
    usr_res <- mulmod(usr_res, usr_factorMultiplier, _1);
    _12 <- 2784;
    tmp276 <@ mload(_12, param_state_memory);
    _13 <- tmp276;
    usr_factorMultiplier <- mulmod(_13, usr_beta, _1);
    usr_factorMultiplier <- addmod(usr_factorMultiplier, usr_gamma, _1);
    _14 <- 2592;
    tmp277 <@ mload(_14, param_state_memory);
    _15 <- tmp277;
    usr_factorMultiplier <- addmod(usr_factorMultiplier, _15, _1);
    usr_res <- mulmod(usr_res, usr_factorMultiplier, _1);
    _16 <- 2816;
    tmp278 <@ mload(_16, param_state_memory);
    _17 <- tmp278;
    usr_factorMultiplier <- mulmod(_17, usr_beta, _1);
    usr_factorMultiplier <- addmod(usr_factorMultiplier, usr_gamma, _1);
    _18 <- 2624;
    tmp279 <@ mload(_18, param_state_memory);
    _19 <- tmp279;
    usr_factorMultiplier <- addmod(usr_factorMultiplier, _19, _1);
    usr_res <- mulmod(usr_res, usr_factorMultiplier, _1);
    _20 <- 2656;
    tmp280 <@ mload(_20, param_state_memory);
    _21 <- tmp280;
    _22 <- addmod(_21, usr_gamma, _1);
    usr_res <- mulmod(usr_res, _22, _1);
    usr_res <- _1 - usr_res;
    _23 <- 4128;
    tmp281 <@ mload(_23, param_state_memory);
    usr_l0AtZ <- tmp281;
    _24 <- 3712;
    tmp282 <@ mload(_24, param_state_memory);
    _25 <- tmp282;
    usr_l0AtZ <- mulmod(usr_l0AtZ, _25, _1);
    _26 <- _1 - usr_l0AtZ;
    usr_res <- addmod(usr_res, _26, _1);
    return usr_res;
    }
  
  proc revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(): unit = {
    var _1, _2;
    _1 <- 0;
    _2 <- _1;
    return ();
    }
  
  proc shift_right_unsigned(value : uint256): uint256 = {
    var newValue, _1;
    _1 <- 224;
    newValue <- _1 >> value;
    return newValue;
    }
  
  proc usr_revertWithMessage(usr_len : uint256, usr_reason : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, _2, _3, _4, _5, _6, _7;
    _1 <- 229 << 4594637;
    _2 <- 0;
    param_state_memory <@ mstore(_2, _1, param_state_memory);
    _3 <- 32;
    _4 <- 4;
    param_state_memory <@ mstore(_4, _3, param_state_memory);
    _5 <- 36;
    param_state_memory <@ mstore(_5, usr_len, param_state_memory);
    _6 <- 68;
    param_state_memory <@ mstore(_6, usr_reason, param_state_memory);
    _7 <- 100;
    return ();
    return param_state_memory;
    }
  
  proc revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490(): unit = {
    var _1;
    _1 <- 0;
    return ();
    }
  
  proc usr_loadProof(param_state_memory : mem): mem = {
    var param_state_memory, _1, usr_offset, tmp95, _2, usr_publicInputLengthInWords, tmp96, _3, usr_isValid, _4, _5, _6, _7, tmp97, _8, _9, tmp98, _10, usr_proofLengthInWords, tmp99, _11, _12, _13, _14, _15, tmp100, usr_x, _16, _17, _18, tmp101, usr_y, usr_xx, _19, _20, _21, _22, _23, _24, _25, _26, _27, _28, tmp102, usr_x_1, _29, _30, _31, tmp103, usr_y_1, usr_xx_1, _32, _33, _34, _35, _36, _37, _38, _39, _40, tmp104, usr_x_2, _41, _42, _43, tmp105, usr_y_2, usr_xx_2, _44, _45, _46, _47, _48, _49, _50, _51, _52, tmp106, usr_x_3, _53, _54, _55, tmp107, usr_y_3, usr_xx_3, _56, _57, _58, _59, _60, _61, _62, _63, _64, tmp108, usr_x_4, _65, _66, _67, tmp109, usr_y_4, usr_xx_4, _68, _69, _70, _71, _72, _73, _74, _75, _76, tmp110, usr_x_5, _77, _78, _79, tmp111, usr_y_5, usr_xx_5, _80, _81, _82, _83, _84, _85, _86, _87, _88, tmp112, usr_x_6, _89, _90, _91, tmp113, usr_y_6, usr_xx_6, _92, _93, _94, _95, _96, _97, _98, _99, _100, tmp114, usr_x_7, _101, _102, _103, tmp115, usr_y_7, usr_xx_7, _104, _105, _106, _107, _108, _109, _110, _111, _112, tmp116, usr_x_8, _113, _114, _115, tmp117, usr_y_8, usr_xx_8, _116, _117, _118, _119, _120, _121, _122, _123, _124, tmp118, usr_x_9, _125, _126, _127, tmp119, usr_y_9, usr_xx_9, _128, _129, _130, _131, _132, _133, _134, _135, _136, tmp120, usr_x_10, _137, _138, _139, tmp121, usr_y_10, usr_xx_10, _140, _141, _142, _143, _144, _145, _146, _147, _148, _149, tmp122, _150, _151, _152, _153, _154, tmp123, _155, _156, _157, _158, _159, tmp124, _160, _161, _162, _163, _164, tmp125, _165, _166, _167, _168, _169, tmp126, _170, _171, _172, _173, _174, tmp127, _175, _176, _177, _178, _179, tmp128, _180, _181, _182, _183, _184, tmp129, _185, _186, _187, _188, _189, tmp130, _190, _191, _192, _193, _194, tmp131, _195, _196, _197, _198, _199, tmp132, _200, _201, _202, _203, _204, tmp133, _205, _206, _207, _208, _209, tmp134, _210, _211, _212, _213, _214, tmp135, _215, _216, _217, _218, _219, tmp136, _220, _221, _222, _223, _224, tmp137, _225, _226, _227, _228, _229, tmp138, _230, _231, _232, _233, _234, tmp139, _235, _236, _237, _238, _239, tmp140, usr_x_11, _240, _241, _242, tmp141, usr_y_11, usr_xx_11, _243, _244, _245, _246, _247, _248, _249, _250, _251, tmp142, usr_x_12, _252, _253, _254, tmp143, usr_y_12, usr_xx_12, _255, _256, _257, _258, _259, _260, tmp144, _261, usr_recursiveProofLengthInWords, tmp145, _262, _263, tmp146, _264, _265, _266, _267, tmp148, usr_x_13, _268, _269, tmp149, usr_y_13, usr_xx_13, _270, _271, _272, _273, _274, _275, _276, _277, tmp150, usr_x_14, _278, _279, tmp151, usr_y_14, usr_xx_14, _280, _281, _282, _283, _284, _285, _286, _287, _288, tmp152;
    _1 <- 4;
    tmp95 <@ calldataload(_1);
    usr_offset <- tmp95;
    _2 <- usr_offset + _1;
    tmp96 <@ calldataload(_2);
    usr_publicInputLengthInWords <- tmp96;
    _3 <- 1;
    usr_isValid <- usr_publicInputLengthInWords = _3;
    _4 <- 253 << 1 - 1;
    _5 <- 36;
    _6 <- usr_offset + _5;
    tmp97 <@ calldataload(_6);
    _7 <- tmp97;
    _8 <- _7 /\ _4;
    _9 <- 1824;
    param_state_memory <@ mstore(_9, _8, param_state_memory);
    tmp98 <@ calldataload(_5);
    usr_offset <- tmp98;
    _10 <- usr_offset + _1;
    tmp99 <@ calldataload(_10);
    usr_proofLengthInWords <- tmp99;
    _11 <- 44;
    _12 <- usr_proofLengthInWords = _11;
    usr_isValid <- _12 /\ usr_isValid;
    _13 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
    _14 <- usr_offset + _5;
    tmp100 <@ calldataload(_14);
    _15 <- tmp100;
    usr_x <- _15 %% _13;
    _16 <- 68;
    _17 <- usr_offset + _16;
    tmp101 <@ calldataload(_17);
    _18 <- tmp101;
    usr_y <- _18 %% _13;
    usr_xx <- mulmod(usr_x, usr_x, _13);
    _19 <- 3;
    _20 <- mulmod(usr_x, usr_xx, _13);
    _21 <- addmod(_20, _19, _13);
    _22 <- mulmod(usr_y, usr_y, _13);
    _23 <- _22 = _21;
    usr_isValid <- _23 /\ usr_isValid;
    _24 <- 1856;
    param_state_memory <@ mstore(_24, usr_x, param_state_memory);
    _25 <- 1888;
    param_state_memory <@ mstore(_25, usr_y, param_state_memory);
    _26 <- 100;
    _27 <- usr_offset + _26;
    tmp102 <@ calldataload(_27);
    _28 <- tmp102;
    usr_x_1 <- _28 %% _13;
    _29 <- 132;
    _30 <- usr_offset + _29;
    tmp103 <@ calldataload(_30);
    _31 <- tmp103;
    usr_y_1 <- _31 %% _13;
    usr_xx_1 <- mulmod(usr_x_1, usr_x_1, _13);
    _32 <- mulmod(usr_x_1, usr_xx_1, _13);
    _33 <- addmod(_32, _19, _13);
    _34 <- mulmod(usr_y_1, usr_y_1, _13);
    _35 <- _34 = _33;
    usr_isValid <- _35 /\ usr_isValid;
    _36 <- 1920;
    param_state_memory <@ mstore(_36, usr_x_1, param_state_memory);
    _37 <- 1952;
    param_state_memory <@ mstore(_37, usr_y_1, param_state_memory);
    _38 <- 164;
    _39 <- usr_offset + _38;
    tmp104 <@ calldataload(_39);
    _40 <- tmp104;
    usr_x_2 <- _40 %% _13;
    _41 <- 196;
    _42 <- usr_offset + _41;
    tmp105 <@ calldataload(_42);
    _43 <- tmp105;
    usr_y_2 <- _43 %% _13;
    usr_xx_2 <- mulmod(usr_x_2, usr_x_2, _13);
    _44 <- mulmod(usr_x_2, usr_xx_2, _13);
    _45 <- addmod(_44, _19, _13);
    _46 <- mulmod(usr_y_2, usr_y_2, _13);
    _47 <- _46 = _45;
    usr_isValid <- _47 /\ usr_isValid;
    _48 <- 1984;
    param_state_memory <@ mstore(_48, usr_x_2, param_state_memory);
    _49 <- 2016;
    param_state_memory <@ mstore(_49, usr_y_2, param_state_memory);
    _50 <- 228;
    _51 <- usr_offset + _50;
    tmp106 <@ calldataload(_51);
    _52 <- tmp106;
    usr_x_3 <- _52 %% _13;
    _53 <- 260;
    _54 <- usr_offset + _53;
    tmp107 <@ calldataload(_54);
    _55 <- tmp107;
    usr_y_3 <- _55 %% _13;
    usr_xx_3 <- mulmod(usr_x_3, usr_x_3, _13);
    _56 <- mulmod(usr_x_3, usr_xx_3, _13);
    _57 <- addmod(_56, _19, _13);
    _58 <- mulmod(usr_y_3, usr_y_3, _13);
    _59 <- _58 = _57;
    usr_isValid <- _59 /\ usr_isValid;
    _60 <- 2048;
    param_state_memory <@ mstore(_60, usr_x_3, param_state_memory);
    _61 <- 2080;
    param_state_memory <@ mstore(_61, usr_y_3, param_state_memory);
    _62 <- 292;
    _63 <- usr_offset + _62;
    tmp108 <@ calldataload(_63);
    _64 <- tmp108;
    usr_x_4 <- _64 %% _13;
    _65 <- 324;
    _66 <- usr_offset + _65;
    tmp109 <@ calldataload(_66);
    _67 <- tmp109;
    usr_y_4 <- _67 %% _13;
    usr_xx_4 <- mulmod(usr_x_4, usr_x_4, _13);
    _68 <- mulmod(usr_x_4, usr_xx_4, _13);
    _69 <- addmod(_68, _19, _13);
    _70 <- mulmod(usr_y_4, usr_y_4, _13);
    _71 <- _70 = _69;
    usr_isValid <- _71 /\ usr_isValid;
    _72 <- 2112;
    param_state_memory <@ mstore(_72, usr_x_4, param_state_memory);
    _73 <- 2144;
    param_state_memory <@ mstore(_73, usr_y_4, param_state_memory);
    _74 <- 356;
    _75 <- usr_offset + _74;
    tmp110 <@ calldataload(_75);
    _76 <- tmp110;
    usr_x_5 <- _76 %% _13;
    _77 <- 388;
    _78 <- usr_offset + _77;
    tmp111 <@ calldataload(_78);
    _79 <- tmp111;
    usr_y_5 <- _79 %% _13;
    usr_xx_5 <- mulmod(usr_x_5, usr_x_5, _13);
    _80 <- mulmod(usr_x_5, usr_xx_5, _13);
    _81 <- addmod(_80, _19, _13);
    _82 <- mulmod(usr_y_5, usr_y_5, _13);
    _83 <- _82 = _81;
    usr_isValid <- _83 /\ usr_isValid;
    _84 <- 2176;
    param_state_memory <@ mstore(_84, usr_x_5, param_state_memory);
    _85 <- 2208;
    param_state_memory <@ mstore(_85, usr_y_5, param_state_memory);
    _86 <- 420;
    _87 <- usr_offset + _86;
    tmp112 <@ calldataload(_87);
    _88 <- tmp112;
    usr_x_6 <- _88 %% _13;
    _89 <- 452;
    _90 <- usr_offset + _89;
    tmp113 <@ calldataload(_90);
    _91 <- tmp113;
    usr_y_6 <- _91 %% _13;
    usr_xx_6 <- mulmod(usr_x_6, usr_x_6, _13);
    _92 <- mulmod(usr_x_6, usr_xx_6, _13);
    _93 <- addmod(_92, _19, _13);
    _94 <- mulmod(usr_y_6, usr_y_6, _13);
    _95 <- _94 = _93;
    usr_isValid <- _95 /\ usr_isValid;
    _96 <- 2240;
    param_state_memory <@ mstore(_96, usr_x_6, param_state_memory);
    _97 <- 2272;
    param_state_memory <@ mstore(_97, usr_y_6, param_state_memory);
    _98 <- 484;
    _99 <- usr_offset + _98;
    tmp114 <@ calldataload(_99);
    _100 <- tmp114;
    usr_x_7 <- _100 %% _13;
    _101 <- 516;
    _102 <- usr_offset + _101;
    tmp115 <@ calldataload(_102);
    _103 <- tmp115;
    usr_y_7 <- _103 %% _13;
    usr_xx_7 <- mulmod(usr_x_7, usr_x_7, _13);
    _104 <- mulmod(usr_x_7, usr_xx_7, _13);
    _105 <- addmod(_104, _19, _13);
    _106 <- mulmod(usr_y_7, usr_y_7, _13);
    _107 <- _106 = _105;
    usr_isValid <- _107 /\ usr_isValid;
    _108 <- 2304;
    param_state_memory <@ mstore(_108, usr_x_7, param_state_memory);
    _109 <- 2336;
    param_state_memory <@ mstore(_109, usr_y_7, param_state_memory);
    _110 <- 548;
    _111 <- usr_offset + _110;
    tmp116 <@ calldataload(_111);
    _112 <- tmp116;
    usr_x_8 <- _112 %% _13;
    _113 <- 580;
    _114 <- usr_offset + _113;
    tmp117 <@ calldataload(_114);
    _115 <- tmp117;
    usr_y_8 <- _115 %% _13;
    usr_xx_8 <- mulmod(usr_x_8, usr_x_8, _13);
    _116 <- mulmod(usr_x_8, usr_xx_8, _13);
    _117 <- addmod(_116, _19, _13);
    _118 <- mulmod(usr_y_8, usr_y_8, _13);
    _119 <- _118 = _117;
    usr_isValid <- _119 /\ usr_isValid;
    _120 <- 2368;
    param_state_memory <@ mstore(_120, usr_x_8, param_state_memory);
    _121 <- 2400;
    param_state_memory <@ mstore(_121, usr_y_8, param_state_memory);
    _122 <- 612;
    _123 <- usr_offset + _122;
    tmp118 <@ calldataload(_123);
    _124 <- tmp118;
    usr_x_9 <- _124 %% _13;
    _125 <- 644;
    _126 <- usr_offset + _125;
    tmp119 <@ calldataload(_126);
    _127 <- tmp119;
    usr_y_9 <- _127 %% _13;
    usr_xx_9 <- mulmod(usr_x_9, usr_x_9, _13);
    _128 <- mulmod(usr_x_9, usr_xx_9, _13);
    _129 <- addmod(_128, _19, _13);
    _130 <- mulmod(usr_y_9, usr_y_9, _13);
    _131 <- _130 = _129;
    usr_isValid <- _131 /\ usr_isValid;
    _132 <- 2432;
    param_state_memory <@ mstore(_132, usr_x_9, param_state_memory);
    _133 <- 2464;
    param_state_memory <@ mstore(_133, usr_y_9, param_state_memory);
    _134 <- 676;
    _135 <- usr_offset + _134;
    tmp120 <@ calldataload(_135);
    _136 <- tmp120;
    usr_x_10 <- _136 %% _13;
    _137 <- 708;
    _138 <- usr_offset + _137;
    tmp121 <@ calldataload(_138);
    _139 <- tmp121;
    usr_y_10 <- _139 %% _13;
    usr_xx_10 <- mulmod(usr_x_10, usr_x_10, _13);
    _140 <- mulmod(usr_x_10, usr_xx_10, _13);
    _141 <- addmod(_140, _19, _13);
    _142 <- mulmod(usr_y_10, usr_y_10, _13);
    _143 <- _142 = _141;
    usr_isValid <- _143 /\ usr_isValid;
    _144 <- 2496;
    param_state_memory <@ mstore(_144, usr_x_10, param_state_memory);
    _145 <- 2528;
    param_state_memory <@ mstore(_145, usr_y_10, param_state_memory);
    _146 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    _147 <- 740;
    _148 <- usr_offset + _147;
    tmp122 <@ calldataload(_148);
    _149 <- tmp122;
    _150 <- _149 %% _146;
    _151 <- 2560;
    param_state_memory <@ mstore(_151, _150, param_state_memory);
    _152 <- 772;
    _153 <- usr_offset + _152;
    tmp123 <@ calldataload(_153);
    _154 <- tmp123;
    _155 <- _154 %% _146;
    _156 <- 2592;
    param_state_memory <@ mstore(_156, _155, param_state_memory);
    _157 <- 804;
    _158 <- usr_offset + _157;
    tmp124 <@ calldataload(_158);
    _159 <- tmp124;
    _160 <- _159 %% _146;
    _161 <- 2624;
    param_state_memory <@ mstore(_161, _160, param_state_memory);
    _162 <- 836;
    _163 <- usr_offset + _162;
    tmp125 <@ calldataload(_163);
    _164 <- tmp125;
    _165 <- _164 %% _146;
    _166 <- 2656;
    param_state_memory <@ mstore(_166, _165, param_state_memory);
    _167 <- 868;
    _168 <- usr_offset + _167;
    tmp126 <@ calldataload(_168);
    _169 <- tmp126;
    _170 <- _169 %% _146;
    _171 <- 2688;
    param_state_memory <@ mstore(_171, _170, param_state_memory);
    _172 <- 900;
    _173 <- usr_offset + _172;
    tmp127 <@ calldataload(_173);
    _174 <- tmp127;
    _175 <- _174 %% _146;
    _176 <- 2720;
    param_state_memory <@ mstore(_176, _175, param_state_memory);
    _177 <- 932;
    _178 <- usr_offset + _177;
    tmp128 <@ calldataload(_178);
    _179 <- tmp128;
    _180 <- _179 %% _146;
    _181 <- 2752;
    param_state_memory <@ mstore(_181, _180, param_state_memory);
    _182 <- 964;
    _183 <- usr_offset + _182;
    tmp129 <@ calldataload(_183);
    _184 <- tmp129;
    _185 <- _184 %% _146;
    _186 <- 2784;
    param_state_memory <@ mstore(_186, _185, param_state_memory);
    _187 <- 996;
    _188 <- usr_offset + _187;
    tmp130 <@ calldataload(_188);
    _189 <- tmp130;
    _190 <- _189 %% _146;
    _191 <- 2816;
    param_state_memory <@ mstore(_191, _190, param_state_memory);
    _192 <- 1028;
    _193 <- usr_offset + _192;
    tmp131 <@ calldataload(_193);
    _194 <- tmp131;
    _195 <- _194 %% _146;
    _196 <- 2848;
    param_state_memory <@ mstore(_196, _195, param_state_memory);
    _197 <- 1060;
    _198 <- usr_offset + _197;
    tmp132 <@ calldataload(_198);
    _199 <- tmp132;
    _200 <- _199 %% _146;
    _201 <- 2880;
    param_state_memory <@ mstore(_201, _200, param_state_memory);
    _202 <- 1092;
    _203 <- usr_offset + _202;
    tmp133 <@ calldataload(_203);
    _204 <- tmp133;
    _205 <- _204 %% _146;
    _206 <- 2912;
    param_state_memory <@ mstore(_206, _205, param_state_memory);
    _207 <- 1124;
    _208 <- usr_offset + _207;
    tmp134 <@ calldataload(_208);
    _209 <- tmp134;
    _210 <- _209 %% _146;
    _211 <- 2944;
    param_state_memory <@ mstore(_211, _210, param_state_memory);
    _212 <- 1156;
    _213 <- usr_offset + _212;
    tmp135 <@ calldataload(_213);
    _214 <- tmp135;
    _215 <- _214 %% _146;
    _216 <- 2976;
    param_state_memory <@ mstore(_216, _215, param_state_memory);
    _217 <- 1188;
    _218 <- usr_offset + _217;
    tmp136 <@ calldataload(_218);
    _219 <- tmp136;
    _220 <- _219 %% _146;
    _221 <- 3008;
    param_state_memory <@ mstore(_221, _220, param_state_memory);
    _222 <- 1220;
    _223 <- usr_offset + _222;
    tmp137 <@ calldataload(_223);
    _224 <- tmp137;
    _225 <- _224 %% _146;
    _226 <- 3040;
    param_state_memory <@ mstore(_226, _225, param_state_memory);
    _227 <- 1252;
    _228 <- usr_offset + _227;
    tmp138 <@ calldataload(_228);
    _229 <- tmp138;
    _230 <- _229 %% _146;
    _231 <- 3072;
    param_state_memory <@ mstore(_231, _230, param_state_memory);
    _232 <- 1284;
    _233 <- usr_offset + _232;
    tmp139 <@ calldataload(_233);
    _234 <- tmp139;
    _235 <- _234 %% _146;
    _236 <- 3104;
    param_state_memory <@ mstore(_236, _235, param_state_memory);
    _237 <- 1316;
    _238 <- usr_offset + _237;
    tmp140 <@ calldataload(_238);
    _239 <- tmp140;
    usr_x_11 <- _239 %% _13;
    _240 <- 1348;
    _241 <- usr_offset + _240;
    tmp141 <@ calldataload(_241);
    _242 <- tmp141;
    usr_y_11 <- _242 %% _13;
    usr_xx_11 <- mulmod(usr_x_11, usr_x_11, _13);
    _243 <- mulmod(usr_x_11, usr_xx_11, _13);
    _244 <- addmod(_243, _19, _13);
    _245 <- mulmod(usr_y_11, usr_y_11, _13);
    _246 <- _245 = _244;
    usr_isValid <- _246 /\ usr_isValid;
    _247 <- 3136;
    param_state_memory <@ mstore(_247, usr_x_11, param_state_memory);
    _248 <- 3168;
    param_state_memory <@ mstore(_248, usr_y_11, param_state_memory);
    _249 <- 1380;
    _250 <- usr_offset + _249;
    tmp142 <@ calldataload(_250);
    _251 <- tmp142;
    usr_x_12 <- _251 %% _13;
    _252 <- 1412;
    _253 <- usr_offset + _252;
    tmp143 <@ calldataload(_253);
    _254 <- tmp143;
    usr_y_12 <- _254 %% _13;
    usr_xx_12 <- mulmod(usr_x_12, usr_x_12, _13);
    _255 <- mulmod(usr_x_12, usr_xx_12, _13);
    _256 <- addmod(_255, _19, _13);
    _257 <- mulmod(usr_y_12, usr_y_12, _13);
    _258 <- _257 = _256;
    usr_isValid <- _258 /\ usr_isValid;
    _259 <- 3200;
    param_state_memory <@ mstore(_259, usr_x_12, param_state_memory);
    _260 <- 3232;
    param_state_memory <@ mstore(_260, usr_y_12, param_state_memory);
    tmp144 <@ calldataload(_16);
    usr_offset <- tmp144;
    _261 <- usr_offset + _1;
    tmp145 <@ calldataload(_261);
    usr_recursiveProofLengthInWords <- tmp145;
    _262 <- 1792;
    tmp146 <@ mload(_262, param_state_memory);
    _263 <- tmp146;
    tmp147 <- _263;
    if (tmp147 = 0)
      {
      _264 <- iszero(usr_recursiveProofLengthInWords);
      usr_isValid <- _264 /\ usr_isValid;
      
      }
    
    else {
      _265 <- usr_recursiveProofLengthInWords = _1;
      usr_isValid <- _265 /\ usr_isValid;
      _266 <- usr_offset + _5;
      tmp148 <@ calldataload(_266);
      _267 <- tmp148;
      usr_x_13 <- _267 %% _13;
      _268 <- usr_offset + _16;
      tmp149 <@ calldataload(_268);
      _269 <- tmp149;
      usr_y_13 <- _269 %% _13;
      usr_xx_13 <- mulmod(usr_x_13, usr_x_13, _13);
      _270 <- mulmod(usr_x_13, usr_xx_13, _13);
      _271 <- addmod(_270, _19, _13);
      _272 <- mulmod(usr_y_13, usr_y_13, _13);
      _273 <- _272 = _271;
      usr_isValid <- _273 /\ usr_isValid;
      _274 <- 3264;
      param_state_memory <@ mstore(_274, usr_x_13, param_state_memory);
      _275 <- 3296;
      param_state_memory <@ mstore(_275, usr_y_13, param_state_memory);
      _276 <- usr_offset + _26;
      tmp150 <@ calldataload(_276);
      _277 <- tmp150;
      usr_x_14 <- _277 %% _13;
      _278 <- usr_offset + _29;
      tmp151 <@ calldataload(_278);
      _279 <- tmp151;
      usr_y_14 <- _279 %% _13;
      usr_xx_14 <- mulmod(usr_x_14, usr_x_14, _13);
      _280 <- mulmod(usr_x_14, usr_xx_14, _13);
      _281 <- addmod(_280, _19, _13);
      _282 <- mulmod(usr_y_14, usr_y_14, _13);
      _283 <- _282 = _281;
      usr_isValid <- _283 /\ usr_isValid;
      _284 <- 3328;
      param_state_memory <@ mstore(_284, usr_x_14, param_state_memory);
      _285 <- 3360;
      param_state_memory <@ mstore(_285, usr_y_14, param_state_memory);
      
      }
    
    _286 <- iszero(usr_isValid);
    if (_286)
      {
      _287 <- "loadProof: Proof is invalid";
      _288 <- 27;
      tmp152,param_state_memory <@ usr_revertWithMessage(_288, _287, param_state_memory);
      
      }
    
    return param_state_memory;
    }
  
  proc usr_mainGateLinearisationContributionWithV(usr_dest : uint256, usr_stateOpening0AtZ : uint256, usr_stateOpening1AtZ : uint256, usr_stateOpening2AtZ : uint256, usr_stateOpening3AtZ : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp295, _2, tmp296, _3, tmp297, _4, tmp298, _5, _6, _7, tmp299, _8, _9, tmp300, _10, tmp301, _11, _12, tmp302, _13, tmp303, _14, _15, tmp304, _16, _17, tmp305, usr_coeff, tmp306;
    _1 <- 512;
    tmp295,param_state_memory <@ usr_pointMulIntoDest(_1, usr_stateOpening0AtZ, usr_dest, param_state_memory);
    _2 <- 576;
    tmp296,param_state_memory <@ usr_pointMulAndAddIntoDest(_2, usr_stateOpening1AtZ, usr_dest, param_state_memory);
    _3 <- 640;
    tmp297,param_state_memory <@ usr_pointMulAndAddIntoDest(_3, usr_stateOpening2AtZ, usr_dest, param_state_memory);
    _4 <- 704;
    tmp298,param_state_memory <@ usr_pointMulAndAddIntoDest(_4, usr_stateOpening3AtZ, usr_dest, param_state_memory);
    _5 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    _6 <- mulmod(usr_stateOpening0AtZ, usr_stateOpening1AtZ, _5);
    _7 <- 768;
    tmp299,param_state_memory <@ usr_pointMulAndAddIntoDest(_7, _6, usr_dest, param_state_memory);
    _8 <- mulmod(usr_stateOpening0AtZ, usr_stateOpening2AtZ, _5);
    _9 <- 832;
    tmp300,param_state_memory <@ usr_pointMulAndAddIntoDest(_9, _8, usr_dest, param_state_memory);
    _10 <- 896;
    tmp301,param_state_memory <@ usr_pointAddAssign(usr_dest, _10, param_state_memory);
    _11 <- 2688;
    tmp302 <@ mload(_11, param_state_memory);
    _12 <- tmp302;
    _13 <- 960;
    tmp303,param_state_memory <@ usr_pointMulAndAddIntoDest(_13, _12, usr_dest, param_state_memory);
    _14 <- 4000;
    tmp304 <@ mload(_14, param_state_memory);
    _15 <- tmp304;
    _16 <- 2720;
    tmp305 <@ mload(_16, param_state_memory);
    _17 <- tmp305;
    usr_coeff <- mulmod(_17, _15, _5);
    tmp306,param_state_memory <@ usr_pointMulIntoDest(usr_dest, usr_coeff, usr_dest, param_state_memory);
    return param_state_memory;
    }
  
  proc cleanup_bool(value : uint256): uint256 = {
    var cleaned, _1;
    _1 <- iszero(value);
    cleaned <- iszero(_1);
    return cleaned;
    }
  
  proc fun_verificationKeyHash(param_state_memory : mem): (uint256 * mem) = {
    var var_vkHash, param_state_memory, tmp47, usr_start, usr_end, _1, _2, usr_length, tmp48;
    pop(zero_value_for_split_bytes32);
    tmp47,param_state_memory <@ fun_loadVerificationKey(param_state_memory);
    usr_start <- 512;
    usr_end <- 1792;
    _1 <- 32;
    _2 <- usr_end - usr_start;
    usr_length <- _2 + _1;
    tmp48 <@ keccak256(usr_start, usr_length);
    var_vkHash <- tmp48;
    return (var_vkHash, param_state_memory);
    }
  
  proc revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d(): unit = {
    var _1;
    _1 <- 0;
    return ();
    }
  
  proc usr_pointSubAssign(usr_p1 : uint256, usr_p2 : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp65, _2, _3, _4, _5, tmp66, _6, tmp67, _7, _8, _9, tmp68, _10, _11, _12, _13, _14, _15, tmp69, _16, tmp70, _17, _18, _19, tmp71;
    tmp65 <@ mload(usr_p1, param_state_memory);
    _1 <- tmp65;
    _2 <- 0;
    param_state_memory <@ mstore(_2, _1, param_state_memory);
    _3 <- 32;
    _4 <- usr_p1 + _3;
    tmp66 <@ mload(_4, param_state_memory);
    _5 <- tmp66;
    param_state_memory <@ mstore(_3, _5, param_state_memory);
    tmp67 <@ mload(usr_p2, param_state_memory);
    _6 <- tmp67;
    _7 <- 64;
    param_state_memory <@ mstore(_7, _6, param_state_memory);
    _8 <- usr_p2 + _3;
    tmp68 <@ mload(_8, param_state_memory);
    _9 <- tmp68;
    _10 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
    _11 <- _10 - _9;
    _12 <- 96;
    param_state_memory <@ mstore(_12, _11, param_state_memory);
    _13 <- 128;
    _14 <- 6;
    tmp69 <@ gas();
    _15 <- tmp69;
    tmp70,param_state_memory <@ staticcall(_15, _14, _2, _13, usr_p1, _7, param_state_memory);
    _16 <- tmp70;
    _17 <- iszero(_16);
    if (_17)
      {
      _18 <- "pointSubAssign: ecAdd failed";
      _19 <- 28;
      tmp71,param_state_memory <@ usr_revertWithMessage(_19, _18, param_state_memory);
      
      }
    
    return param_state_memory;
    }
  
  proc _BODY(): unit = {
    tmp0 <@ memoryguard(128);
    _1 <- tmp0;
    _2 <- 64;
    mstore(_2, _1);
    tmp1 <@ callvalue();
    _3 <- tmp1;
    if (_3)
      {
      tmp2 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb();
      
      }
    
    tmp3 <@ constructor_Verifier();
    tmp4 <@ allocate_unbounded();
    _4 <- tmp4;
    tmp5 <@ datasize("Verifier_1261_deployed");
    _5 <- tmp5;
    tmp6 <@ dataoffset("Verifier_1261_deployed");
    _6 <- tmp6;
    codecopy(_4, _6, _5);
    _7 <- _5;
    return (_4, _5);
    }
  
  proc usr_updateTranscript(usr_value : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, _2, _3, _4, _5, usr_newState0, tmp92, _6, usr_newState1, tmp93, _7, _8;
    _1 <- 0;
    _2 <- 3395;
    param_state_memory <@ mstore8(_2, _1, param_state_memory);
    _3 <- 3460;
    param_state_memory <@ mstore(_3, usr_value, param_state_memory);
    _4 <- 100;
    _5 <- 3392;
    tmp92 <@ keccak256(_5, _4);
    usr_newState0 <- tmp92;
    _6 <- 1;
    param_state_memory <@ mstore8(_2, _6, param_state_memory);
    tmp93 <@ keccak256(_5, _4);
    usr_newState1 <- tmp93;
    _7 <- 3428;
    param_state_memory <@ mstore(_7, usr_newState1, param_state_memory);
    _8 <- 3396;
    param_state_memory <@ mstore(_8, usr_newState0, param_state_memory);
    return param_state_memory;
    }
  
  proc usr_prepareQueries(param_state_memory : mem): mem = {
    var param_state_memory, _1, usr_zInDomainSize, tmp350, usr_currentZ, _2, _3, tmp351, _4, _5, _6, tmp352, _7, _8, tmp353, _9, _10, tmp354, _11, tmp355, _12, usr_stateOpening0AtZ, tmp356, _13, usr_stateOpening1AtZ, tmp357, _14, usr_stateOpening2AtZ, tmp358, _15, usr_stateOpening3AtZ, tmp359, _16, tmp360, tmp361, tmp362, tmp363, _17, _18, tmp364, _19, _20, _21, tmp365, _22, _23, usr_eta, tmp366, usr_currentEta, _24, tmp367, _25, tmp368, _26, tmp369;
    _1 <- 4192;
    tmp350 <@ mload(_1, param_state_memory);
    usr_zInDomainSize <- tmp350;
    usr_currentZ <- usr_zInDomainSize;
    _2 <- 2304;
    tmp351 <@ mload(_2, param_state_memory);
    _3 <- tmp351;
    _4 <- 4288;
    param_state_memory <@ mstore(_4, _3, param_state_memory);
    _5 <- 2336;
    tmp352 <@ mload(_5, param_state_memory);
    _6 <- tmp352;
    _7 <- 4320;
    param_state_memory <@ mstore(_7, _6, param_state_memory);
    _8 <- 2368;
    tmp353,param_state_memory <@ usr_pointMulAndAddIntoDest(_8, usr_zInDomainSize, _4, param_state_memory);
    _9 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    usr_currentZ <- mulmod(usr_zInDomainSize, usr_zInDomainSize, _9);
    _10 <- 2432;
    tmp354,param_state_memory <@ usr_pointMulAndAddIntoDest(_10, usr_currentZ, _4, param_state_memory);
    usr_currentZ <- mulmod(usr_currentZ, usr_zInDomainSize, _9);
    _11 <- 2496;
    tmp355,param_state_memory <@ usr_pointMulAndAddIntoDest(_11, usr_currentZ, _4, param_state_memory);
    _12 <- 2560;
    tmp356 <@ mload(_12, param_state_memory);
    usr_stateOpening0AtZ <- tmp356;
    _13 <- 2592;
    tmp357 <@ mload(_13, param_state_memory);
    usr_stateOpening1AtZ <- tmp357;
    _14 <- 2624;
    tmp358 <@ mload(_14, param_state_memory);
    usr_stateOpening2AtZ <- tmp358;
    _15 <- 2656;
    tmp359 <@ mload(_15, param_state_memory);
    usr_stateOpening3AtZ <- tmp359;
    _16 <- 4352;
    tmp360,param_state_memory <@ usr_mainGateLinearisationContributionWithV(_16, usr_stateOpening0AtZ, usr_stateOpening1AtZ, usr_stateOpening2AtZ, usr_stateOpening3AtZ, param_state_memory);
    tmp361,param_state_memory <@ usr_addAssignRescueCustomGateLinearisationContributionWithV(_16, usr_stateOpening0AtZ, usr_stateOpening1AtZ, usr_stateOpening2AtZ, usr_stateOpening3AtZ, param_state_memory);
    tmp362,param_state_memory <@ usr_addAssignPermutationLinearisationContributionWithV(_16, usr_stateOpening0AtZ, usr_stateOpening1AtZ, usr_stateOpening2AtZ, usr_stateOpening3AtZ, param_state_memory);
    tmp363,param_state_memory <@ usr_addAssignLookupLinearisationContributionWithV(_16, usr_stateOpening0AtZ, usr_stateOpening1AtZ, usr_stateOpening2AtZ, param_state_memory);
    _17 <- 1472;
    tmp364 <@ mload(_17, param_state_memory);
    _18 <- tmp364;
    _19 <- 4416;
    param_state_memory <@ mstore(_19, _18, param_state_memory);
    _20 <- 1504;
    tmp365 <@ mload(_20, param_state_memory);
    _21 <- tmp365;
    _22 <- 4448;
    param_state_memory <@ mstore(_22, _21, param_state_memory);
    _23 <- 3840;
    tmp366 <@ mload(_23, param_state_memory);
    usr_eta <- tmp366;
    usr_currentEta <- usr_eta;
    _24 <- 1536;
    tmp367,param_state_memory <@ usr_pointMulAndAddIntoDest(_24, usr_eta, _19, param_state_memory);
    usr_currentEta <- mulmod(usr_eta, usr_eta, _9);
    _25 <- 1600;
    tmp368,param_state_memory <@ usr_pointMulAndAddIntoDest(_25, usr_currentEta, _19, param_state_memory);
    usr_currentEta <- mulmod(usr_currentEta, usr_eta, _9);
    _26 <- 1664;
    tmp369,param_state_memory <@ usr_pointMulAndAddIntoDest(_26, usr_currentEta, _19, param_state_memory);
    return param_state_memory;
    }
  
  proc usr_prepareAggregatedCommitment(param_state_memory : mem): mem = {
    var param_state_memory, usr_aggregationChallenge, usr_firstDCoeff, usr_firstTCoeff, _1, _2, tmp377, _3, _4, _5, tmp378, _6, _7, usr_aggregatedOpeningAtZ, tmp379, _8, tmp380, _9, _10, _11, tmp381, _12, _13, tmp382, _14, _15, _16, tmp383, _17, _18, tmp384, _19, _20, tmp385, _21, tmp386, _22, _23, tmp387, _24, _25, _26, tmp388, _27, _28, tmp389, _29, _30, tmp390, _31, _32, tmp391, _33, tmp392, _34, _35, tmp393, _36, _37, _38, tmp394, _39, _40, tmp395, _41, _42, tmp396, _43, _44, tmp397, _45, _46, _47, tmp398, usr_copyPermutationCoeff, _48, _49, tmp399, _50, _51, tmp400, usr_aggregatedOpeningAtZOmega, _52, _53, tmp401, _54, _55, tmp402, _56, _57, tmp403, _58, _59, tmp404, _60, _61, tmp405, _62, _63, tmp406, _64, usr_u, tmp407, _65, tmp408, _66, tmp409, _67, tmp410, _68, usr_aggregatedValue, _69, _70, _71, _72, tmp411;
    usr_aggregationChallenge <- 1;
    _1 <- 4288;
    tmp377 <@ mload(_1, param_state_memory);
    _2 <- tmp377;
    _3 <- 4480;
    param_state_memory <@ mstore(_3, _2, param_state_memory);
    _4 <- 4320;
    tmp378 <@ mload(_4, param_state_memory);
    _5 <- tmp378;
    _6 <- 4512;
    param_state_memory <@ mstore(_6, _5, param_state_memory);
    _7 <- 3072;
    tmp379 <@ mload(_7, param_state_memory);
    usr_aggregatedOpeningAtZ <- tmp379;
    _8 <- 4352;
    tmp380,param_state_memory <@ usr_pointAddIntoDest(_3, _8, _3, param_state_memory);
    _9 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    _10 <- 4000;
    tmp381 <@ mload(_10, param_state_memory);
    _11 <- tmp381;
    usr_aggregationChallenge <- mulmod(usr_aggregationChallenge, _11, _9);
    _12 <- 3104;
    tmp382 <@ mload(_12, param_state_memory);
    _13 <- tmp382;
    _14 <- mulmod(usr_aggregationChallenge, _13, _9);
    usr_aggregatedOpeningAtZ <- addmod(usr_aggregatedOpeningAtZ, _14, _9);
    _15 <- 2560;
    _16 <- 1856;
    tmp383,param_state_memory <@ usr_updateAggregationChallenge(_16, _15, usr_aggregationChallenge, usr_aggregatedOpeningAtZ, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZ <- tmp383;
    _17 <- 2592;
    _18 <- 1920;
    tmp384,param_state_memory <@ usr_updateAggregationChallenge(_18, _17, usr_aggregationChallenge, usr_aggregatedOpeningAtZ, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZ <- tmp384;
    _19 <- 2624;
    _20 <- 1984;
    tmp385,param_state_memory <@ usr_updateAggregationChallenge(_20, _19, usr_aggregationChallenge, usr_aggregatedOpeningAtZ, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZ <- tmp385;
    tmp386 <@ mload(_10, param_state_memory);
    _21 <- tmp386;
    usr_aggregationChallenge <- mulmod(usr_aggregationChallenge, _21, _9);
    usr_firstDCoeff <- usr_aggregationChallenge;
    _22 <- 2656;
    tmp387 <@ mload(_22, param_state_memory);
    _23 <- tmp387;
    _24 <- mulmod(usr_aggregationChallenge, _23, _9);
    usr_aggregatedOpeningAtZ <- addmod(usr_aggregatedOpeningAtZ, _24, _9);
    _25 <- 2720;
    _26 <- 1024;
    tmp388,param_state_memory <@ usr_updateAggregationChallenge(_26, _25, usr_aggregationChallenge, usr_aggregatedOpeningAtZ, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZ <- tmp388;
    _27 <- 2752;
    _28 <- 1152;
    tmp389,param_state_memory <@ usr_updateAggregationChallenge(_28, _27, usr_aggregationChallenge, usr_aggregatedOpeningAtZ, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZ <- tmp389;
    _29 <- 2784;
    _30 <- 1216;
    tmp390,param_state_memory <@ usr_updateAggregationChallenge(_30, _29, usr_aggregationChallenge, usr_aggregatedOpeningAtZ, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZ <- tmp390;
    _31 <- 2816;
    _32 <- 1280;
    tmp391,param_state_memory <@ usr_updateAggregationChallenge(_32, _31, usr_aggregationChallenge, usr_aggregatedOpeningAtZ, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZ <- tmp391;
    tmp392 <@ mload(_10, param_state_memory);
    _33 <- tmp392;
    usr_aggregationChallenge <- mulmod(usr_aggregationChallenge, _33, _9);
    usr_firstTCoeff <- usr_aggregationChallenge;
    _34 <- 2944;
    tmp393 <@ mload(_34, param_state_memory);
    _35 <- tmp393;
    _36 <- mulmod(usr_aggregationChallenge, _35, _9);
    usr_aggregatedOpeningAtZ <- addmod(usr_aggregatedOpeningAtZ, _36, _9);
    _37 <- 3008;
    _38 <- 1408;
    tmp394,param_state_memory <@ usr_updateAggregationChallenge(_38, _37, usr_aggregationChallenge, usr_aggregatedOpeningAtZ, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZ <- tmp394;
    _39 <- 3040;
    _40 <- 1728;
    tmp395,param_state_memory <@ usr_updateAggregationChallenge(_40, _39, usr_aggregationChallenge, usr_aggregatedOpeningAtZ, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZ <- tmp395;
    _41 <- 4608;
    param_state_memory <@ mstore(_41, usr_aggregatedOpeningAtZ, param_state_memory);
    tmp396 <@ mload(_10, param_state_memory);
    _42 <- tmp396;
    usr_aggregationChallenge <- mulmod(usr_aggregationChallenge, _42, _9);
    _43 <- 4032;
    tmp397 <@ mload(_43, param_state_memory);
    _44 <- tmp397;
    _45 <- mulmod(usr_aggregationChallenge, _44, _9);
    _46 <- 4928;
    tmp398 <@ mload(_46, param_state_memory);
    _47 <- tmp398;
    usr_copyPermutationCoeff <- addmod(_47, _45, _9);
    _48 <- 4544;
    _49 <- 2112;
    tmp399,param_state_memory <@ usr_pointMulIntoDest(_49, usr_copyPermutationCoeff, _48, param_state_memory);
    _50 <- 2848;
    tmp400 <@ mload(_50, param_state_memory);
    _51 <- tmp400;
    usr_aggregatedOpeningAtZOmega <- mulmod(_51, usr_aggregationChallenge, _9);
    _52 <- 2688;
    _53 <- 2048;
    tmp401,param_state_memory <@ usr_updateAggregationChallenge_105(_53, _52, usr_firstDCoeff, usr_aggregationChallenge, usr_aggregatedOpeningAtZOmega, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZOmega <- tmp401;
    _54 <- 4992;
    tmp402 <@ mload(_54, param_state_memory);
    _55 <- tmp402;
    _56 <- 2880;
    _57 <- 2176;
    tmp403,param_state_memory <@ usr_updateAggregationChallenge_105(_57, _56, _55, usr_aggregationChallenge, usr_aggregatedOpeningAtZOmega, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZOmega <- tmp403;
    _58 <- 4960;
    tmp404 <@ mload(_58, param_state_memory);
    _59 <- tmp404;
    _60 <- 2912;
    _61 <- 2240;
    tmp405,param_state_memory <@ usr_updateAggregationChallenge_105(_61, _60, _59, usr_aggregationChallenge, usr_aggregatedOpeningAtZOmega, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZOmega <- tmp405;
    _62 <- 2976;
    _63 <- 4416;
    tmp406,param_state_memory <@ usr_updateAggregationChallenge_105(_63, _62, usr_firstTCoeff, usr_aggregationChallenge, usr_aggregatedOpeningAtZOmega, param_state_memory);
    usr_aggregationChallenge,usr_aggregatedOpeningAtZOmega <- tmp406;
    _64 <- 4640;
    param_state_memory <@ mstore(_64, usr_aggregatedOpeningAtZOmega, param_state_memory);
    tmp407 <@ mload(_43, param_state_memory);
    usr_u <- tmp407;
    _65 <- 4736;
    tmp408,param_state_memory <@ usr_pointAddIntoDest(_3, _48, _65, param_state_memory);
    tmp409 <@ mload(_41, param_state_memory);
    _66 <- tmp409;
    tmp410 <@ mload(_64, param_state_memory);
    _67 <- tmp410;
    _68 <- mulmod(_67, usr_u, _9);
    usr_aggregatedValue <- addmod(_68, _66, _9);
    _69 <- 1;
    _70 <- 4672;
    param_state_memory <@ mstore(_70, _69, param_state_memory);
    _71 <- 2;
    _72 <- 4704;
    param_state_memory <@ mstore(_72, _71, param_state_memory);
    tmp411,param_state_memory <@ usr_pointMulIntoDest(_70, usr_aggregatedValue, _70, param_state_memory);
    return param_state_memory;
    }
  
  proc abi_encode_bool_to_bool(value : uint256, pos : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp31;
    tmp31 <@ cleanup_bool(value);
    _1 <- tmp31;
    param_state_memory <@ mstore(pos, _1, param_state_memory);
    return param_state_memory;
    }
  
  proc constructor_IVerifier(): unit = {
    }
  
  proc _BODY(): unit = {
    var zero_bool, tmp434, tmp435, tmp436, tmp437, tmp438, tmp439, tmp440, _1, _2, _3;
    _1 <- 128;
    _2 <- 64;
    mstore(_2, _1);
    _3 <- 4;
    tmp9 <@ calldatasize();
    _4 <- tmp9;
    _5 <- lt(_4, _3);
    _6 <- iszero(_5);
    if (_6)
      {
      _7 <- 0;
      tmp10 <@ calldataload(_7);
      _8 <- tmp10;
      tmp11 <@ shift_right_unsigned(_8);
      selector <- tmp11;
      tmp12 <- selector;
      if (tmp12 = 2279198755)
        {
        tmp13 <@ external_fun_verify();
        
        }
      
      else {
        if (tmp12 = 2659796434)
          {
          tmp14 <@ external_fun_verificationKeyHash();
          
          }
        
        
        }
      
      
      }
    
    tmp15 <@ revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74();
    }
  
  proc usr_verifyQuotientEvaluation(param_state_memory : mem): mem = {
    var param_state_memory, _1, usr_alpha, tmp253, _2, usr_currentAlpha, _3, _4, _5, _6, _7, _8, _9, _10, usr_stateZ, tmp254, _11, _12, tmp255, _13, _14, _15, _16, _17, tmp256, _18, _19, _20, tmp257, _21, tmp258, usr_stateT, _22, _23, tmp259, usr_result, _24, tmp260, _25, tmp261, _26, _27, tmp262, _28, _29, _30, tmp263, usr_vanishing, _31, _32, tmp264, usr_lhs, _33, _34, _35, _36, tmp265;
    _1 <- 3520;
    tmp253 <@ mload(_1, param_state_memory);
    usr_alpha <- tmp253;
    _2 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    usr_currentAlpha <- mulmod(usr_alpha, usr_alpha, _2);
    _3 <- 3616;
    param_state_memory <@ mstore(_3, usr_currentAlpha, param_state_memory);
    usr_currentAlpha <- mulmod(usr_currentAlpha, usr_alpha, _2);
    _4 <- 3648;
    param_state_memory <@ mstore(_4, usr_currentAlpha, param_state_memory);
    usr_currentAlpha <- mulmod(usr_currentAlpha, usr_alpha, _2);
    _5 <- 3680;
    param_state_memory <@ mstore(_5, usr_currentAlpha, param_state_memory);
    usr_currentAlpha <- mulmod(usr_currentAlpha, usr_alpha, _2);
    _6 <- 3712;
    param_state_memory <@ mstore(_6, usr_currentAlpha, param_state_memory);
    usr_currentAlpha <- mulmod(usr_currentAlpha, usr_alpha, _2);
    _7 <- 3744;
    param_state_memory <@ mstore(_7, usr_currentAlpha, param_state_memory);
    usr_currentAlpha <- mulmod(usr_currentAlpha, usr_alpha, _2);
    _8 <- 3776;
    param_state_memory <@ mstore(_8, usr_currentAlpha, param_state_memory);
    usr_currentAlpha <- mulmod(usr_currentAlpha, usr_alpha, _2);
    _9 <- 3808;
    param_state_memory <@ mstore(_9, usr_currentAlpha, param_state_memory);
    _10 <- 4064;
    tmp254 <@ mload(_10, param_state_memory);
    usr_stateZ <- tmp254;
    _11 <- 0;
    tmp255,param_state_memory <@ usr_evaluateLagrangePolyOutOfDomain(_11, usr_stateZ, param_state_memory);
    _12 <- tmp255;
    _13 <- 4128;
    param_state_memory <@ mstore(_13, _12, param_state_memory);
    _14 <- 1;
    _15 <- 67108864;
    _16 <- _15 - _14;
    tmp256,param_state_memory <@ usr_evaluateLagrangePolyOutOfDomain(_16, usr_stateZ, param_state_memory);
    _17 <- tmp256;
    _18 <- 4160;
    param_state_memory <@ mstore(_18, _17, param_state_memory);
    _19 <- 1824;
    tmp257 <@ mload(_19, param_state_memory);
    _20 <- tmp257;
    tmp258 <@ mload(_13, param_state_memory);
    _21 <- tmp258;
    usr_stateT <- mulmod(_21, _20, _2);
    _22 <- 2720;
    tmp259 <@ mload(_22, param_state_memory);
    _23 <- tmp259;
    usr_result <- mulmod(usr_stateT, _23, _2);
    tmp260 <@ usr_permutationQuotientContribution(param_state_memory);
    _24 <- tmp260;
    usr_result <- addmod(usr_result, _24, _2);
    tmp261,param_state_memory <@ usr_lookupQuotientContribution(param_state_memory);
    _25 <- tmp261;
    usr_result <- addmod(usr_result, _25, _2);
    _26 <- 3104;
    tmp262 <@ mload(_26, param_state_memory);
    _27 <- tmp262;
    usr_result <- addmod(_27, usr_result, _2);
    _28 <- _2 - _14;
    _29 <- 4192;
    tmp263 <@ mload(_29, param_state_memory);
    _30 <- tmp263;
    usr_vanishing <- addmod(_30, _28, _2);
    _31 <- 3072;
    tmp264 <@ mload(_31, param_state_memory);
    _32 <- tmp264;
    usr_lhs <- mulmod(_32, usr_vanishing, _2);
    _33 <- usr_lhs = usr_result;
    _34 <- iszero(_33);
    if (_34)
      {
      _35 <- "invalid quotient evaluation";
      _36 <- 27;
      tmp265,param_state_memory <@ usr_revertWithMessage(_36, _35, param_state_memory);
      
      }
    
    return param_state_memory;
    }
  
  proc revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef(): unit = {
    var _1;
    _1 <- 0;
    return ();
    }
  
  proc usr_getTranscriptChallenge(usr_numberOfChallenge : uint256, param_state_memory : mem): (uint256 * mem) = {
    var usr_challenge, param_state_memory, _1, _2, _3, _4, _5, _6, _7, _8, _9, tmp94;
    _1 <- 2;
    _2 <- 3395;
    param_state_memory <@ mstore8(_2, _1, param_state_memory);
    _3 <- 224;
    _4 <- _3 << usr_numberOfChallenge;
    _5 <- 3460;
    param_state_memory <@ mstore(_5, _4, param_state_memory);
    _6 <- 253 << 1 - 1;
    _7 <- 72;
    _8 <- 3392;
    tmp94 <@ keccak256(_8, _7);
    _9 <- tmp94;
    usr_challenge <- _9 /\ _6;
    return (usr_challenge, param_state_memory);
    }
  
  proc revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74(): unit = {
    var _1;
    _1 <- 0;
    return ();
    }
  
  proc usr_updateAggregationChallenge_105(usr_queriesCommitmentPoint : uint256, usr_valueAtZ_Omega : uint256, usr_previousCoeff : uint256, usr_curAggregationChallenge : uint256, usr_curAggregatedOpeningAtZ_Omega : uint256, param_state_memory : mem): (uint256 * uint256 * mem) = {
    var usr_newAggregationChallenge, usr_newAggregatedOpeningAtZ_Omega, param_state_memory, _1, _2, _3, tmp373, _4, _5, tmp374, _6, usr_finalCoeff, _7, tmp375, _8, tmp376, _9;
    _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    _2 <- 4000;
    tmp373 <@ mload(_2, param_state_memory);
    _3 <- tmp373;
    usr_newAggregationChallenge <- mulmod(usr_curAggregationChallenge, _3, _1);
    _4 <- 4032;
    tmp374 <@ mload(_4, param_state_memory);
    _5 <- tmp374;
    _6 <- mulmod(usr_newAggregationChallenge, _5, _1);
    usr_finalCoeff <- addmod(usr_previousCoeff, _6, _1);
    _7 <- 4544;
    tmp375,param_state_memory <@ usr_pointMulAndAddIntoDest(usr_queriesCommitmentPoint, usr_finalCoeff, _7, param_state_memory);
    tmp376 <@ mload(usr_valueAtZ_Omega, param_state_memory);
    _8 <- tmp376;
    _9 <- mulmod(usr_newAggregationChallenge, _8, _1);
    usr_newAggregatedOpeningAtZ_Omega <- addmod(usr_curAggregatedOpeningAtZ_Omega, _9, _1);
    return (usr_newAggregationChallenge, usr_newAggregatedOpeningAtZ_Omega, param_state_memory);
    }
  
  proc revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(): unit = {
    var _1;
    _1 <- 0;
    return ();
    }
  
  proc abi_encode_bool(headStart : uint256, value0 : uint256, param_state_memory : mem): (uint256 * mem) = {
    var tail, param_state_memory, _1, _2, _3, tmp32;
    _1 <- 32;
    tail <- headStart + _1;
    _2 <- 0;
    _3 <- headStart + _2;
    tmp32,param_state_memory <@ abi_encode_bool_to_bool(value0, _3, param_state_memory);
    return (tail, param_state_memory);
    }
  
  proc abi_encode_bytes32_to_bytes32(value : uint256, pos : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1;
    _1 <- cleanup_bytes32(value);
    param_state_memory <@ mstore(pos, _1, param_state_memory);
    return param_state_memory;
    }
  
  proc usr_addAssignRescueCustomGateLinearisationContributionWithV(usr_dest : uint256, usr_stateOpening0AtZ : uint256, usr_stateOpening1AtZ : uint256, usr_stateOpening2AtZ : uint256, usr_stateOpening3AtZ : uint256, param_state_memory : mem): mem = {
    var param_state_memory, usr_accumulator, usr_intermediateValue, _1, _2, _3, _4, tmp307, _5, _6, _7, tmp308, _8, _9, _10, tmp309, _11, _12, tmp310, _13, tmp311;
    _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    usr_accumulator <- mulmod(usr_stateOpening0AtZ, usr_stateOpening0AtZ, _1);
    _2 <- _1 - usr_stateOpening1AtZ;
    usr_accumulator <- addmod(usr_accumulator, _2, _1);
    _3 <- 3520;
    tmp307 <@ mload(_3, param_state_memory);
    _4 <- tmp307;
    usr_accumulator <- mulmod(usr_accumulator, _4, _1);
    usr_intermediateValue <- mulmod(usr_stateOpening1AtZ, usr_stateOpening1AtZ, _1);
    _5 <- _1 - usr_stateOpening2AtZ;
    usr_intermediateValue <- addmod(usr_intermediateValue, _5, _1);
    _6 <- 3616;
    tmp308 <@ mload(_6, param_state_memory);
    _7 <- tmp308;
    usr_intermediateValue <- mulmod(usr_intermediateValue, _7, _1);
    usr_accumulator <- addmod(usr_accumulator, usr_intermediateValue, _1);
    usr_intermediateValue <- mulmod(usr_stateOpening2AtZ, usr_stateOpening0AtZ, _1);
    _8 <- _1 - usr_stateOpening3AtZ;
    usr_intermediateValue <- addmod(usr_intermediateValue, _8, _1);
    _9 <- 3648;
    tmp309 <@ mload(_9, param_state_memory);
    _10 <- tmp309;
    usr_intermediateValue <- mulmod(usr_intermediateValue, _10, _1);
    usr_accumulator <- addmod(usr_accumulator, usr_intermediateValue, _1);
    _11 <- 4000;
    tmp310 <@ mload(_11, param_state_memory);
    _12 <- tmp310;
    usr_accumulator <- mulmod(usr_accumulator, _12, _1);
    _13 <- 1088;
    tmp311,param_state_memory <@ usr_pointMulAndAddIntoDest(_13, usr_accumulator, usr_dest, param_state_memory);
    return param_state_memory;
    }
  
  proc external_fun_verificationKeyHash(param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp40, tmp41, _2, tmp42, _3, tmp43, ret, tmp44, memPos, tmp45, memEnd, tmp46, _4;
    tmp40 <@ callvalue();
    _1 <- tmp40;
    if (_1)
      {
      tmp41 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb();
      
      }
    
    tmp42 <@ calldatasize();
    _2 <- tmp42;
    _3 <- 4;
    tmp43 <@ abi_decode(_3, _2);
    tmp44,param_state_memory <@ fun_verificationKeyHash(param_state_memory);
    ret <- tmp44;
    tmp45 <@ allocate_unbounded(param_state_memory);
    memPos <- tmp45;
    tmp46,param_state_memory <@ abi_encode_bytes32(memPos, ret, param_state_memory);
    memEnd <- tmp46;
    _4 <- memEnd - memPos;
    return (memPos, _4);
    return param_state_memory;
    }
  
  proc usr_pointAddAssign(usr_p1 : uint256, usr_p2 : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp72, _2, _3, _4, _5, tmp73, _6, tmp74, _7, _8, _9, tmp75, _10, _11, _12, _13, tmp76, _14, tmp77, _15, _16, _17, tmp78;
    tmp72 <@ mload(usr_p1, param_state_memory);
    _1 <- tmp72;
    _2 <- 0;
    param_state_memory <@ mstore(_2, _1, param_state_memory);
    _3 <- 32;
    _4 <- usr_p1 + _3;
    tmp73 <@ mload(_4, param_state_memory);
    _5 <- tmp73;
    param_state_memory <@ mstore(_3, _5, param_state_memory);
    tmp74 <@ mload(usr_p2, param_state_memory);
    _6 <- tmp74;
    _7 <- 64;
    param_state_memory <@ mstore(_7, _6, param_state_memory);
    _8 <- usr_p2 + _3;
    tmp75 <@ mload(_8, param_state_memory);
    _9 <- tmp75;
    _10 <- 96;
    param_state_memory <@ mstore(_10, _9, param_state_memory);
    _11 <- 128;
    _12 <- 6;
    tmp76 <@ gas();
    _13 <- tmp76;
    tmp77,param_state_memory <@ staticcall(_13, _12, _2, _11, usr_p1, _7, param_state_memory);
    _14 <- tmp77;
    _15 <- iszero(_14);
    if (_15)
      {
      _16 <- "pointAddAssign: ecAdd failed";
      _17 <- 28;
      tmp78,param_state_memory <@ usr_revertWithMessage(_17, _16, param_state_memory);
      
      }
    
    return param_state_memory;
    }
  
  proc usr_pointAddIntoDest(usr_p1 : uint256, usr_p2 : uint256, usr_dest : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp58, _2, _3, _4, _5, tmp59, _6, tmp60, _7, _8, _9, tmp61, _10, _11, _12, _13, tmp62, _14, tmp63, _15, _16, _17, tmp64;
    tmp58 <@ mload(usr_p1, param_state_memory);
    _1 <- tmp58;
    _2 <- 0;
    param_state_memory <@ mstore(_2, _1, param_state_memory);
    _3 <- 32;
    _4 <- usr_p1 + _3;
    tmp59 <@ mload(_4, param_state_memory);
    _5 <- tmp59;
    param_state_memory <@ mstore(_3, _5, param_state_memory);
    tmp60 <@ mload(usr_p2, param_state_memory);
    _6 <- tmp60;
    _7 <- 64;
    param_state_memory <@ mstore(_7, _6, param_state_memory);
    _8 <- usr_p2 + _3;
    tmp61 <@ mload(_8, param_state_memory);
    _9 <- tmp61;
    _10 <- 96;
    param_state_memory <@ mstore(_10, _9, param_state_memory);
    _11 <- 128;
    _12 <- 6;
    tmp62 <@ gas();
    _13 <- tmp62;
    tmp63,param_state_memory <@ staticcall(_13, _12, _2, _11, usr_dest, _7, param_state_memory);
    _14 <- tmp63;
    _15 <- iszero(_14);
    if (_15)
      {
      _16 <- "pointAddIntoDest: ecAdd failed";
      _17 <- 30;
      tmp64,param_state_memory <@ usr_revertWithMessage(_17, _16, param_state_memory);
      
      }
    
    return param_state_memory;
    }
  
  proc usr_evaluateLagrangePolyOutOfDomain(usr_polyNum : uint256, usr_at : uint256, param_state_memory : mem): (uint256 * mem) = {
    var usr_res, param_state_memory, usr_omegaPower, _1, tmp266, _2, _3, _4, _5, _6, tmp267, _7, _8, _9, tmp268, _10, usr_denominator, _11, _12, tmp269;
    usr_omegaPower <- 1;
    if (usr_polyNum)
      {
      _1 <- 13446667982376394161563610564587413125564757801019538732601045199901075958935;
      tmp266,param_state_memory <@ usr_modexp(_1, usr_polyNum, param_state_memory);
      usr_omegaPower <- tmp266;
      
      }
    
    _2 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    _3 <- 1;
    _4 <- _2 - _3;
    _5 <- 67108864;
    tmp267,param_state_memory <@ usr_modexp(usr_at, _5, param_state_memory);
    _6 <- tmp267;
    usr_res <- addmod(_6, _4, _2);
    _7 <- iszero(usr_res);
    if (_7)
      {
      _8 <- "invalid vanishing polynomial";
      _9 <- 28;
      tmp268,param_state_memory <@ usr_revertWithMessage(_9, _8, param_state_memory);
      
      }
    
    usr_res <- mulmod(usr_res, usr_omegaPower, _2);
    _10 <- _2 - usr_omegaPower;
    usr_denominator <- addmod(usr_at, _10, _2);
    usr_denominator <- mulmod(usr_denominator, _5, _2);
    _11 <- 2;
    _12 <- _2 - _11;
    tmp269,param_state_memory <@ usr_modexp(usr_denominator, _12, param_state_memory);
    usr_denominator <- tmp269;
    usr_res <- mulmod(usr_res, usr_denominator, _2);
    return (usr_res, param_state_memory);
    }
  
  proc usr_initializeTranscript(param_state_memory : mem): mem = {
    var param_state_memory, _1, _2, tmp153, tmp154, _3, _4, tmp155, tmp156, _5, _6, tmp157, tmp158, _7, _8, tmp159, tmp160, _9, _10, tmp161, tmp162, _11, _12, tmp163, tmp164, _13, _14, tmp165, tmp166, _15, _16, tmp167, tmp168, _17, _18, tmp169, tmp170, _19, _20, tmp171, _21, _22, _23, tmp172, tmp173, _24, _25, tmp174, tmp175, _26, _27, tmp176, _28, _29, _30, tmp177, _31, _32, _33, tmp178, tmp179, _34, _35, tmp180, tmp181, _36, _37, tmp182, _38, _39, _40, tmp183, _41, _42, _43, tmp184, tmp185, _44, _45, tmp186, tmp187, _46, _47, tmp188, _48, _49, _50, tmp189, tmp190, _51, _52, tmp191, tmp192, _53, _54, tmp193, tmp194, _55, _56, tmp195, tmp196, _57, _58, tmp197, tmp198, _59, _60, tmp199, tmp200, _61, _62, tmp201, tmp202, _63, _64, tmp203, tmp204, _65, usr_z, tmp205, _66, _67, _68, tmp206, _69, _70, _71, tmp207, tmp208, _72, _73, tmp209, tmp210, _74, _75, tmp211, tmp212, _76, _77, tmp213, tmp214, _78, _79, tmp215, tmp216, _80, _81, tmp217, tmp218, _82, _83, tmp219, tmp220, _84, _85, tmp221, tmp222, _86, _87, tmp223, tmp224, _88, _89, tmp225, tmp226, _90, _91, tmp227, tmp228, _92, _93, tmp229, tmp230, _94, _95, tmp231, tmp232, _96, _97, tmp233, tmp234, _98, _99, tmp235, tmp236, _100, _101, tmp237, tmp238, _102, _103, tmp239, tmp240, _104, _105, tmp241, tmp242, _106, _107, tmp243, _108, _109, _110, tmp244, tmp245, _111, _112, tmp246, tmp247, _113, _114, tmp248, tmp249, _115, _116, tmp250, tmp251, _117, _118, tmp252, _119;
    _1 <- 1824;
    tmp153 <@ mload(_1, param_state_memory);
    _2 <- tmp153;
    tmp154,param_state_memory <@ usr_updateTranscript(_2, param_state_memory);
    _3 <- 1856;
    tmp155 <@ mload(_3, param_state_memory);
    _4 <- tmp155;
    tmp156,param_state_memory <@ usr_updateTranscript(_4, param_state_memory);
    _5 <- 1888;
    tmp157 <@ mload(_5, param_state_memory);
    _6 <- tmp157;
    tmp158,param_state_memory <@ usr_updateTranscript(_6, param_state_memory);
    _7 <- 1920;
    tmp159 <@ mload(_7, param_state_memory);
    _8 <- tmp159;
    tmp160,param_state_memory <@ usr_updateTranscript(_8, param_state_memory);
    _9 <- 1952;
    tmp161 <@ mload(_9, param_state_memory);
    _10 <- tmp161;
    tmp162,param_state_memory <@ usr_updateTranscript(_10, param_state_memory);
    _11 <- 1984;
    tmp163 <@ mload(_11, param_state_memory);
    _12 <- tmp163;
    tmp164,param_state_memory <@ usr_updateTranscript(_12, param_state_memory);
    _13 <- 2016;
    tmp165 <@ mload(_13, param_state_memory);
    _14 <- tmp165;
    tmp166,param_state_memory <@ usr_updateTranscript(_14, param_state_memory);
    _15 <- 2048;
    tmp167 <@ mload(_15, param_state_memory);
    _16 <- tmp167;
    tmp168,param_state_memory <@ usr_updateTranscript(_16, param_state_memory);
    _17 <- 2080;
    tmp169 <@ mload(_17, param_state_memory);
    _18 <- tmp169;
    tmp170,param_state_memory <@ usr_updateTranscript(_18, param_state_memory);
    _19 <- 0;
    tmp171,param_state_memory <@ usr_getTranscriptChallenge(_19, param_state_memory);
    _20 <- tmp171;
    _21 <- 3840;
    param_state_memory <@ mstore(_21, _20, param_state_memory);
    _22 <- 2176;
    tmp172 <@ mload(_22, param_state_memory);
    _23 <- tmp172;
    tmp173,param_state_memory <@ usr_updateTranscript(_23, param_state_memory);
    _24 <- 2208;
    tmp174 <@ mload(_24, param_state_memory);
    _25 <- tmp174;
    tmp175,param_state_memory <@ usr_updateTranscript(_25, param_state_memory);
    _26 <- 1;
    tmp176,param_state_memory <@ usr_getTranscriptChallenge(_26, param_state_memory);
    _27 <- tmp176;
    _28 <- 3552;
    param_state_memory <@ mstore(_28, _27, param_state_memory);
    _29 <- 2;
    tmp177,param_state_memory <@ usr_getTranscriptChallenge(_29, param_state_memory);
    _30 <- tmp177;
    _31 <- 3584;
    param_state_memory <@ mstore(_31, _30, param_state_memory);
    _32 <- 2112;
    tmp178 <@ mload(_32, param_state_memory);
    _33 <- tmp178;
    tmp179,param_state_memory <@ usr_updateTranscript(_33, param_state_memory);
    _34 <- 2144;
    tmp180 <@ mload(_34, param_state_memory);
    _35 <- tmp180;
    tmp181,param_state_memory <@ usr_updateTranscript(_35, param_state_memory);
    _36 <- 3;
    tmp182,param_state_memory <@ usr_getTranscriptChallenge(_36, param_state_memory);
    _37 <- tmp182;
    _38 <- 3872;
    param_state_memory <@ mstore(_38, _37, param_state_memory);
    _39 <- 4;
    tmp183,param_state_memory <@ usr_getTranscriptChallenge(_39, param_state_memory);
    _40 <- tmp183;
    _41 <- 3904;
    param_state_memory <@ mstore(_41, _40, param_state_memory);
    _42 <- 2240;
    tmp184 <@ mload(_42, param_state_memory);
    _43 <- tmp184;
    tmp185,param_state_memory <@ usr_updateTranscript(_43, param_state_memory);
    _44 <- 2272;
    tmp186 <@ mload(_44, param_state_memory);
    _45 <- tmp186;
    tmp187,param_state_memory <@ usr_updateTranscript(_45, param_state_memory);
    _46 <- 5;
    tmp188,param_state_memory <@ usr_getTranscriptChallenge(_46, param_state_memory);
    _47 <- tmp188;
    _48 <- 3520;
    param_state_memory <@ mstore(_48, _47, param_state_memory);
    _49 <- 2304;
    tmp189 <@ mload(_49, param_state_memory);
    _50 <- tmp189;
    tmp190,param_state_memory <@ usr_updateTranscript(_50, param_state_memory);
    _51 <- 2336;
    tmp191 <@ mload(_51, param_state_memory);
    _52 <- tmp191;
    tmp192,param_state_memory <@ usr_updateTranscript(_52, param_state_memory);
    _53 <- 2368;
    tmp193 <@ mload(_53, param_state_memory);
    _54 <- tmp193;
    tmp194,param_state_memory <@ usr_updateTranscript(_54, param_state_memory);
    _55 <- 2400;
    tmp195 <@ mload(_55, param_state_memory);
    _56 <- tmp195;
    tmp196,param_state_memory <@ usr_updateTranscript(_56, param_state_memory);
    _57 <- 2432;
    tmp197 <@ mload(_57, param_state_memory);
    _58 <- tmp197;
    tmp198,param_state_memory <@ usr_updateTranscript(_58, param_state_memory);
    _59 <- 2464;
    tmp199 <@ mload(_59, param_state_memory);
    _60 <- tmp199;
    tmp200,param_state_memory <@ usr_updateTranscript(_60, param_state_memory);
    _61 <- 2496;
    tmp201 <@ mload(_61, param_state_memory);
    _62 <- tmp201;
    tmp202,param_state_memory <@ usr_updateTranscript(_62, param_state_memory);
    _63 <- 2528;
    tmp203 <@ mload(_63, param_state_memory);
    _64 <- tmp203;
    tmp204,param_state_memory <@ usr_updateTranscript(_64, param_state_memory);
    _65 <- 6;
    tmp205,param_state_memory <@ usr_getTranscriptChallenge(_65, param_state_memory);
    usr_z <- tmp205;
    _66 <- 4064;
    param_state_memory <@ mstore(_66, usr_z, param_state_memory);
    _67 <- 67108864;
    tmp206,param_state_memory <@ usr_modexp(usr_z, _67, param_state_memory);
    _68 <- tmp206;
    _69 <- 4192;
    param_state_memory <@ mstore(_69, _68, param_state_memory);
    _70 <- 3072;
    tmp207 <@ mload(_70, param_state_memory);
    _71 <- tmp207;
    tmp208,param_state_memory <@ usr_updateTranscript(_71, param_state_memory);
    _72 <- 2560;
    tmp209 <@ mload(_72, param_state_memory);
    _73 <- tmp209;
    tmp210,param_state_memory <@ usr_updateTranscript(_73, param_state_memory);
    _74 <- 2592;
    tmp211 <@ mload(_74, param_state_memory);
    _75 <- tmp211;
    tmp212,param_state_memory <@ usr_updateTranscript(_75, param_state_memory);
    _76 <- 2624;
    tmp213 <@ mload(_76, param_state_memory);
    _77 <- tmp213;
    tmp214,param_state_memory <@ usr_updateTranscript(_77, param_state_memory);
    _78 <- 2656;
    tmp215 <@ mload(_78, param_state_memory);
    _79 <- tmp215;
    tmp216,param_state_memory <@ usr_updateTranscript(_79, param_state_memory);
    _80 <- 2688;
    tmp217 <@ mload(_80, param_state_memory);
    _81 <- tmp217;
    tmp218,param_state_memory <@ usr_updateTranscript(_81, param_state_memory);
    _82 <- 2720;
    tmp219 <@ mload(_82, param_state_memory);
    _83 <- tmp219;
    tmp220,param_state_memory <@ usr_updateTranscript(_83, param_state_memory);
    _84 <- 2752;
    tmp221 <@ mload(_84, param_state_memory);
    _85 <- tmp221;
    tmp222,param_state_memory <@ usr_updateTranscript(_85, param_state_memory);
    _86 <- 2784;
    tmp223 <@ mload(_86, param_state_memory);
    _87 <- tmp223;
    tmp224,param_state_memory <@ usr_updateTranscript(_87, param_state_memory);
    _88 <- 2816;
    tmp225 <@ mload(_88, param_state_memory);
    _89 <- tmp225;
    tmp226,param_state_memory <@ usr_updateTranscript(_89, param_state_memory);
    _90 <- 2848;
    tmp227 <@ mload(_90, param_state_memory);
    _91 <- tmp227;
    tmp228,param_state_memory <@ usr_updateTranscript(_91, param_state_memory);
    _92 <- 2944;
    tmp229 <@ mload(_92, param_state_memory);
    _93 <- tmp229;
    tmp230,param_state_memory <@ usr_updateTranscript(_93, param_state_memory);
    _94 <- 3008;
    tmp231 <@ mload(_94, param_state_memory);
    _95 <- tmp231;
    tmp232,param_state_memory <@ usr_updateTranscript(_95, param_state_memory);
    _96 <- 3040;
    tmp233 <@ mload(_96, param_state_memory);
    _97 <- tmp233;
    tmp234,param_state_memory <@ usr_updateTranscript(_97, param_state_memory);
    _98 <- 2880;
    tmp235 <@ mload(_98, param_state_memory);
    _99 <- tmp235;
    tmp236,param_state_memory <@ usr_updateTranscript(_99, param_state_memory);
    _100 <- 2912;
    tmp237 <@ mload(_100, param_state_memory);
    _101 <- tmp237;
    tmp238,param_state_memory <@ usr_updateTranscript(_101, param_state_memory);
    _102 <- 2976;
    tmp239 <@ mload(_102, param_state_memory);
    _103 <- tmp239;
    tmp240,param_state_memory <@ usr_updateTranscript(_103, param_state_memory);
    _104 <- 3104;
    tmp241 <@ mload(_104, param_state_memory);
    _105 <- tmp241;
    tmp242,param_state_memory <@ usr_updateTranscript(_105, param_state_memory);
    _106 <- 7;
    tmp243,param_state_memory <@ usr_getTranscriptChallenge(_106, param_state_memory);
    _107 <- tmp243;
    _108 <- 4000;
    param_state_memory <@ mstore(_108, _107, param_state_memory);
    _109 <- 3136;
    tmp244 <@ mload(_109, param_state_memory);
    _110 <- tmp244;
    tmp245,param_state_memory <@ usr_updateTranscript(_110, param_state_memory);
    _111 <- 3168;
    tmp246 <@ mload(_111, param_state_memory);
    _112 <- tmp246;
    tmp247,param_state_memory <@ usr_updateTranscript(_112, param_state_memory);
    _113 <- 3200;
    tmp248 <@ mload(_113, param_state_memory);
    _114 <- tmp248;
    tmp249,param_state_memory <@ usr_updateTranscript(_114, param_state_memory);
    _115 <- 3232;
    tmp250 <@ mload(_115, param_state_memory);
    _116 <- tmp250;
    tmp251,param_state_memory <@ usr_updateTranscript(_116, param_state_memory);
    _117 <- 8;
    tmp252,param_state_memory <@ usr_getTranscriptChallenge(_117, param_state_memory);
    _118 <- tmp252;
    _119 <- 4032;
    param_state_memory <@ mstore(_119, _118, param_state_memory);
    return param_state_memory;
    }
  
  proc revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(): unit = {
    var _1;
    _1 <- 0;
    return ();
    }
  
  proc abi_encode_bytes32(headStart : uint256, value0 : uint256, param_state_memory : mem): (uint256 * mem) = {
    var tail, param_state_memory, _1, _2, _3, tmp39;
    _1 <- 32;
    tail <- headStart + _1;
    _2 <- 0;
    _3 <- headStart + _2;
    tmp39,param_state_memory <@ abi_encode_bytes32_to_bytes32(value0, _3, param_state_memory);
    return (tail, param_state_memory);
    }
  
  proc abi_decode_array_uint256_dyn_calldata(offset : uint256, end : uint256): (uint256 * uint256) = {
    var arrayPos, length, _1, _2, _3, _4, tmp17, tmp18, _5, _6, tmp19, _7, _8, _9, _10, tmp20;
    _1 <- 31;
    _2 <- offset + _1;
    _3 <- slt(_2, end);
    _4 <- iszero(_3);
    if (_4)
      {
      tmp17 <@ revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d();
      
      }
    
    tmp18 <@ calldataload(offset);
    length <- tmp18;
    _5 <- 18446744073709551615;
    _6 <- gt(length, _5);
    if (_6)
      {
      tmp19 <@ revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490();
      
      }
    
    _7 <- 32;
    arrayPos <- offset + _7;
    _8 <- length * _7;
    _9 <- arrayPos + _8;
    _10 <- gt(_9, end);
    if (_10)
      {
      tmp20 <@ revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef();
      
      }
    
    return (arrayPos, length);
    }
  
  proc abi_decode(headStart : uint256, dataEnd : uint256): unit = {
    var _1, _2, _3, tmp38;
    _1 <- 0;
    _2 <- dataEnd - headStart;
    _3 <- slt(_2, _1);
    if (_3)
      {
      tmp38 <@ revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b();
      
      }
    
    }
  
  proc usr_pointNegate(usr_point : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, _2, usr_pY, tmp88, _3, tmp90, _4, _5, tmp91, _6, _7;
    _1 <- 32;
    _2 <- usr_point + _1;
    tmp88 <@ mload(_2, param_state_memory);
    usr_pY <- tmp88;
    tmp89 <- usr_pY;
    if (tmp89 = 0)
      {
      tmp90 <@ mload(usr_point, param_state_memory);
      _3 <- tmp90;
      if (_3)
        {
        _4 <- "pointNegate: invalid point";
        _5 <- 26;
        tmp91,param_state_memory <@ usr_revertWithMessage(_5, _4, param_state_memory);
        
        }
      
      
      }
    
    else {
      _6 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
      _7 <- _6 - usr_pY;
      param_state_memory <@ mstore(_2, _7, param_state_memory);
      
      }
    
    return param_state_memory;
    }
  
  proc allocate_unbounded(param_state_memory : mem): uint256 = {
    var memPtr, _1, tmp7;
    _1 <- 64;
    tmp7 <@ mload(_1, param_state_memory);
    memPtr <- tmp7;
    return memPtr;
    }
  
  
  }.
(* End Verifier_1261 *)
