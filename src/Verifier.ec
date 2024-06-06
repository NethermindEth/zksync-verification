(* Begin Verifier_1261 *)
op zero_value_for_split_bytes32: uint256 = 0.

op zero_value_for_split_bool: uint256 = 0.

op cleanup_bytes32(value : uint256): uint256 = value.

module Verifier_1261 = {
  proc fun_verify(var__offset : uint256, var_length : uint256, var_offset : uint256, var__length : uint256, var_1250_offset : uint256, var_1250_length : uint256): uint256 = {
    var var, zero_bool, TMP618, TMP619, TMP620, TMP621, TMP622, TMP623, TMP624, _1, _2, TMP625, _3;
      {
      zero_bool <- zero_value_for_split_bool;
      var <- zero_bool;
      TMP618 <@ fun_loadVerificationKey();
      TMP618;
      TMP619 <@ usr$loadProof();
      TMP619;
      TMP620 <@ usr$initializeTranscript();
      TMP620;
      TMP621 <@ usr$verifyQuotientEvaluation();
      TMP621;
      TMP622 <@ usr$prepareQueries();
      TMP622;
      TMP623 <@ usr$prepareAggregatedCommitment();
      TMP623;
      TMP624 <@ usr$finalPairing();
      TMP624;
      _1 <- true;
      _2 <- 0;
      TMP625 <@ MStore(_2, _1);
      TMP625;
      _3 <- 32;
      return (_2, _3);
      return var;
      
      }
    }
  
  proc usr$updateAggregationChallenge_105(usr$queriesCommitmentPoint : uint256, usr$valueAtZ_Omega : uint256, usr$previousCoeff : uint256, usr$curAggregationChallenge : uint256, usr$curAggregatedOpeningAtZ_Omega : uint256): (uint256 * uint256) = {
    var usr$newAggregationChallenge, usr$newAggregatedOpeningAtZ_Omega, _1, _2, _3, TMP537, _4, _5, TMP538, _6, usr$finalCoeff, _7, TMP539, _8, TMP540, _9;
      {
      _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _2 <- 4000;
      TMP537 <@ MLoad(_2);
      _3 <- TMP537;
      usr$newAggregationChallenge <- mulmod(usr$curAggregationChallenge, _3, _1);
      _4 <- 4032;
      TMP538 <@ MLoad(_4);
      _5 <- TMP538;
      _6 <- mulmod(usr$newAggregationChallenge, _5, _1);
      usr$finalCoeff <- addmod(usr$previousCoeff, _6, _1);
      _7 <- 4544;
      TMP539 <@ usr$pointMulAndAddIntoDest(usr$queriesCommitmentPoint, usr$finalCoeff, _7);
      TMP539;
      TMP540 <@ MLoad(usr$valueAtZ_Omega);
      _8 <- TMP540;
      _9 <- mulmod(usr$newAggregationChallenge, _8, _1);
      usr$newAggregatedOpeningAtZ_Omega <- addmod(usr$curAggregatedOpeningAtZ_Omega, _9, _1);
      return (usr$newAggregationChallenge, usr$newAggregatedOpeningAtZ_Omega);
      
      }
    }
  
  proc usr$pointMulAndAddIntoDest(usr$point : uint256, usr$s : uint256, usr$dest : uint256): unit = {
    var _1, TMP152, _2, TMP153, _3, _4, _5, TMP154, TMP155, _6, TMP156, _7, _8, _9, TMP157, usr$success, TMP158, _10, TMP159, TMP160, _11, _12, TMP161, TMP162, _13, _14, _15, TMP163, _16, TMP164, _17, _18, _19, TMP165;
      {
      TMP152 <@ MLoad(usr$point);
      _1 <- TMP152;
      _2 <- 0;
      TMP153 <@ MStore(_2, _1);
      TMP153;
      _3 <- 32;
      _4 <- usr$point + _3;
      TMP154 <@ MLoad(_4);
      _5 <- TMP154;
      TMP155 <@ MStore(_3, _5);
      TMP155;
      _6 <- 64;
      TMP156 <@ MStore(_6, usr$s);
      TMP156;
      _7 <- 96;
      _8 <- 7;
      TMP157 <@ Gas();
      _9 <- TMP157;
      TMP158 <@ StaticCall(_9, _8, _2, _7, _2, _6);
      usr$success <- TMP158;
      TMP159 <@ MLoad(usr$dest);
      _10 <- TMP159;
      TMP160 <@ MStore(_6, _10);
      TMP160;
      _11 <- usr$dest + _3;
      TMP161 <@ MLoad(_11);
      _12 <- TMP161;
      TMP162 <@ MStore(_7, _12);
      TMP162;
      _13 <- 128;
      _14 <- 6;
      TMP163 <@ Gas();
      _15 <- TMP163;
      TMP164 <@ StaticCall(_15, _14, _2, _13, usr$dest, _6);
      _16 <- TMP164;
      usr$success <- usr$success /\ _16;
      _17 <- iszero(usr$success);
      if (_17)
        {
        _18 <- "pointMulAndAddIntoDest";
        _19 <- 22;
        TMP165 <@ usr$revertWithMessage(_19, _18);
        TMP165;
        
        }
      ;
      
      }
    }
  
  proc revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc constructor_Verifier(): unit = {
    var TMP10;
      {
      TMP10 <@ constructor_IVerifier();
      TMP10;
      
      }
    }
  
  proc usr$getTranscriptChallenge(usr$numberOfChallenge : uint256): uint256 = {
    var usr$challenge, _1, _2, TMP178, _3, _4, _5, TMP179, _6, _7, _8, _9, TMP180;
      {
      _1 <- 2;
      _2 <- 3395;
      TMP178 <@ MStore8(_2, _1);
      TMP178;
      _3 <- 224;
      _4 <- _3 << usr$numberOfChallenge;
      _5 <- 3460;
      TMP179 <@ MStore(_5, _4);
      TMP179;
      _6 <- 253 << 1 - 1;
      _7 <- 72;
      _8 <- 3392;
      TMP180 <@ Keccak256(_8, _7);
      _9 <- TMP180;
      usr$challenge <- _9 /\ _6;
      return usr$challenge;
      
      }
    }
  
  proc abi_encode_bytes32(headStart : uint256, value0 : uint256): uint256 = {
    var tail, _1, _2, _3, TMP45;
      {
      _1 <- 32;
      tail <- headStart + _1;
      _2 <- 0;
      _3 <- headStart + _2;
      TMP45 <@ abi_encode_bytes32_to_bytes32(value0, _3);
      TMP45;
      return tail;
      
      }
    }
  
  proc usr$addAssignLookupLinearisationContributionWithV(usr$dest : uint256, usr$stateOpening0AtZ : uint256, usr$stateOpening1AtZ : uint256, usr$stateOpening2AtZ : uint256): unit = {
    var _1, usr$factor, TMP488, _2, TMP489, _3, TMP490, _4, _5, TMP491, _6, TMP492, _7, TMP493, _8, _9, TMP494, _10, _11, TMP495, _12, _13, TMP496, usr$fReconstructed, _14, usr$eta, TMP497, usr$currentEta, _15, _16, _17, _18, TMP498, _19, _20, _21, TMP499, _22, _23, TMP500, _24, _25, TMP501, _26, TMP502, _27, TMP503, _28, _29, TMP504, _30, _31, TMP505, _32, _33, _34, TMP506, _35, _36, TMP507, _37, _38, TMP508, _39, TMP509;
      {
      _1 <- 2912;
      TMP488 <@ MLoad(_1);
      usr$factor <- TMP488;
      TMP489 <@ MLoad(3744);
      _2 <- TMP489;
      usr$factor <- mulmod(usr$factor, _2, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      TMP490 <@ MLoad(4096);
      _3 <- TMP490;
      usr$factor <- mulmod(usr$factor, _3, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _4 <- 4000;
      TMP491 <@ MLoad(_4);
      _5 <- TMP491;
      usr$factor <- mulmod(usr$factor, _5, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _6 <- 4992;
      TMP492 <@ MStore(_6, usr$factor);
      TMP492;
      _7 <- 2976;
      TMP493 <@ MLoad(_7);
      usr$factor <- TMP493;
      _8 <- 3872;
      TMP494 <@ MLoad(_8);
      _9 <- TMP494;
      usr$factor <- mulmod(usr$factor, _9, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _10 <- 2944;
      TMP495 <@ MLoad(_10);
      _11 <- TMP495;
      usr$factor <- addmod(usr$factor, _11, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _12 <- 3968;
      TMP496 <@ MLoad(_12);
      _13 <- TMP496;
      usr$factor <- addmod(usr$factor, _13, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$fReconstructed <- usr$stateOpening0AtZ;
      _14 <- 3840;
      TMP497 <@ MLoad(_14);
      usr$eta <- TMP497;
      usr$currentEta <- usr$eta;
      _15 <- mulmod(usr$eta, usr$stateOpening1AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$fReconstructed <- addmod(usr$stateOpening0AtZ, _15, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$currentEta <- mulmod(usr$eta, usr$eta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _16 <- mulmod(usr$currentEta, usr$stateOpening2AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$fReconstructed <- addmod(usr$fReconstructed, _16, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$currentEta <- mulmod(usr$currentEta, usr$eta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _17 <- 3040;
      TMP498 <@ MLoad(_17);
      _18 <- TMP498;
      _19 <- mulmod(_18, usr$currentEta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$fReconstructed <- addmod(usr$fReconstructed, _19, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _20 <- 3008;
      TMP499 <@ MLoad(_20);
      _21 <- TMP499;
      usr$fReconstructed <- mulmod(usr$fReconstructed, _21, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _22 <- 3904;
      TMP500 <@ MLoad(_22);
      _23 <- TMP500;
      usr$fReconstructed <- addmod(usr$fReconstructed, _23, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$fReconstructed, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _24 <- 3936;
      TMP501 <@ MLoad(_24);
      _25 <- TMP501;
      usr$factor <- mulmod(usr$factor, _25, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- 21888242871839275222246405745257275088548364400416034343698204186575808495617 - usr$factor;
      TMP502 <@ MLoad(3744);
      _26 <- TMP502;
      usr$factor <- mulmod(usr$factor, _26, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      TMP503 <@ MLoad(4096);
      _27 <- TMP503;
      usr$factor <- mulmod(usr$factor, _27, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _28 <- 3776;
      TMP504 <@ MLoad(_28);
      _29 <- TMP504;
      _30 <- 4128;
      TMP505 <@ MLoad(_30);
      _31 <- TMP505;
      _32 <- mulmod(_31, _29, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- addmod(usr$factor, _32, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _33 <- 3808;
      TMP506 <@ MLoad(_33);
      _34 <- TMP506;
      _35 <- 4160;
      TMP507 <@ MLoad(_35);
      _36 <- TMP507;
      _37 <- mulmod(_36, _34, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- addmod(usr$factor, _37, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      TMP508 <@ MLoad(_4);
      _38 <- TMP508;
      usr$factor <- mulmod(usr$factor, _38, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _39 <- 4960;
      TMP509 <@ MStore(_39, usr$factor);
      TMP509;
      
      }
    }
  
  proc usr$initializeTranscript(): unit = {
    var _1, _2, TMP288, TMP289, _3, _4, TMP290, TMP291, _5, _6, TMP292, TMP293, _7, _8, TMP294, TMP295, _9, _10, TMP296, TMP297, _11, _12, TMP298, TMP299, _13, _14, TMP300, TMP301, _15, _16, TMP302, TMP303, _17, _18, TMP304, TMP305, _19, _20, TMP306, _21, TMP307, _22, _23, TMP308, TMP309, _24, _25, TMP310, TMP311, _26, _27, TMP312, _28, TMP313, _29, _30, TMP314, _31, TMP315, _32, _33, TMP316, TMP317, _34, _35, TMP318, TMP319, _36, _37, TMP320, _38, TMP321, _39, _40, TMP322, _41, TMP323, _42, _43, TMP324, TMP325, _44, _45, TMP326, TMP327, _46, _47, TMP328, _48, TMP329, _49, _50, TMP330, TMP331, _51, _52, TMP332, TMP333, _53, _54, TMP334, TMP335, _55, _56, TMP336, TMP337, _57, _58, TMP338, TMP339, _59, _60, TMP340, TMP341, _61, _62, TMP342, TMP343, _63, _64, TMP344, TMP345, _65, usr$z, TMP346, _66, TMP347, _67, _68, TMP348, _69, TMP349, _70, _71, TMP350, TMP351, _72, _73, TMP352, TMP353, _74, _75, TMP354, TMP355, _76, _77, TMP356, TMP357, _78, _79, TMP358, TMP359, _80, _81, TMP360, TMP361, _82, _83, TMP362, TMP363, _84, _85, TMP364, TMP365, _86, _87, TMP366, TMP367, _88, _89, TMP368, TMP369, _90, _91, TMP370, TMP371, _92, _93, TMP372, TMP373, _94, _95, TMP374, TMP375, _96, _97, TMP376, TMP377, _98, _99, TMP378, TMP379, _100, _101, TMP380, TMP381, _102, _103, TMP382, TMP383, _104, _105, TMP384, TMP385, _106, _107, TMP386, _108, TMP387, _109, _110, TMP388, TMP389, _111, _112, TMP390, TMP391, _113, _114, TMP392, TMP393, _115, _116, TMP394, TMP395, _117, _118, TMP396, _119, TMP397;
      {
      _1 <- 1824;
      TMP288 <@ MLoad(_1);
      _2 <- TMP288;
      TMP289 <@ usr$updateTranscript(_2);
      TMP289;
      _3 <- 1856;
      TMP290 <@ MLoad(_3);
      _4 <- TMP290;
      TMP291 <@ usr$updateTranscript(_4);
      TMP291;
      _5 <- 1888;
      TMP292 <@ MLoad(_5);
      _6 <- TMP292;
      TMP293 <@ usr$updateTranscript(_6);
      TMP293;
      _7 <- 1920;
      TMP294 <@ MLoad(_7);
      _8 <- TMP294;
      TMP295 <@ usr$updateTranscript(_8);
      TMP295;
      _9 <- 1952;
      TMP296 <@ MLoad(_9);
      _10 <- TMP296;
      TMP297 <@ usr$updateTranscript(_10);
      TMP297;
      _11 <- 1984;
      TMP298 <@ MLoad(_11);
      _12 <- TMP298;
      TMP299 <@ usr$updateTranscript(_12);
      TMP299;
      _13 <- 2016;
      TMP300 <@ MLoad(_13);
      _14 <- TMP300;
      TMP301 <@ usr$updateTranscript(_14);
      TMP301;
      _15 <- 2048;
      TMP302 <@ MLoad(_15);
      _16 <- TMP302;
      TMP303 <@ usr$updateTranscript(_16);
      TMP303;
      _17 <- 2080;
      TMP304 <@ MLoad(_17);
      _18 <- TMP304;
      TMP305 <@ usr$updateTranscript(_18);
      TMP305;
      _19 <- 0;
      TMP306 <@ usr$getTranscriptChallenge(_19);
      _20 <- TMP306;
      _21 <- 3840;
      TMP307 <@ MStore(_21, _20);
      TMP307;
      _22 <- 2176;
      TMP308 <@ MLoad(_22);
      _23 <- TMP308;
      TMP309 <@ usr$updateTranscript(_23);
      TMP309;
      _24 <- 2208;
      TMP310 <@ MLoad(_24);
      _25 <- TMP310;
      TMP311 <@ usr$updateTranscript(_25);
      TMP311;
      _26 <- 1;
      TMP312 <@ usr$getTranscriptChallenge(_26);
      _27 <- TMP312;
      _28 <- 3552;
      TMP313 <@ MStore(_28, _27);
      TMP313;
      _29 <- 2;
      TMP314 <@ usr$getTranscriptChallenge(_29);
      _30 <- TMP314;
      _31 <- 3584;
      TMP315 <@ MStore(_31, _30);
      TMP315;
      _32 <- 2112;
      TMP316 <@ MLoad(_32);
      _33 <- TMP316;
      TMP317 <@ usr$updateTranscript(_33);
      TMP317;
      _34 <- 2144;
      TMP318 <@ MLoad(_34);
      _35 <- TMP318;
      TMP319 <@ usr$updateTranscript(_35);
      TMP319;
      _36 <- 3;
      TMP320 <@ usr$getTranscriptChallenge(_36);
      _37 <- TMP320;
      _38 <- 3872;
      TMP321 <@ MStore(_38, _37);
      TMP321;
      _39 <- 4;
      TMP322 <@ usr$getTranscriptChallenge(_39);
      _40 <- TMP322;
      _41 <- 3904;
      TMP323 <@ MStore(_41, _40);
      TMP323;
      _42 <- 2240;
      TMP324 <@ MLoad(_42);
      _43 <- TMP324;
      TMP325 <@ usr$updateTranscript(_43);
      TMP325;
      _44 <- 2272;
      TMP326 <@ MLoad(_44);
      _45 <- TMP326;
      TMP327 <@ usr$updateTranscript(_45);
      TMP327;
      _46 <- 5;
      TMP328 <@ usr$getTranscriptChallenge(_46);
      _47 <- TMP328;
      _48 <- 3520;
      TMP329 <@ MStore(_48, _47);
      TMP329;
      _49 <- 2304;
      TMP330 <@ MLoad(_49);
      _50 <- TMP330;
      TMP331 <@ usr$updateTranscript(_50);
      TMP331;
      _51 <- 2336;
      TMP332 <@ MLoad(_51);
      _52 <- TMP332;
      TMP333 <@ usr$updateTranscript(_52);
      TMP333;
      _53 <- 2368;
      TMP334 <@ MLoad(_53);
      _54 <- TMP334;
      TMP335 <@ usr$updateTranscript(_54);
      TMP335;
      _55 <- 2400;
      TMP336 <@ MLoad(_55);
      _56 <- TMP336;
      TMP337 <@ usr$updateTranscript(_56);
      TMP337;
      _57 <- 2432;
      TMP338 <@ MLoad(_57);
      _58 <- TMP338;
      TMP339 <@ usr$updateTranscript(_58);
      TMP339;
      _59 <- 2464;
      TMP340 <@ MLoad(_59);
      _60 <- TMP340;
      TMP341 <@ usr$updateTranscript(_60);
      TMP341;
      _61 <- 2496;
      TMP342 <@ MLoad(_61);
      _62 <- TMP342;
      TMP343 <@ usr$updateTranscript(_62);
      TMP343;
      _63 <- 2528;
      TMP344 <@ MLoad(_63);
      _64 <- TMP344;
      TMP345 <@ usr$updateTranscript(_64);
      TMP345;
      _65 <- 6;
      TMP346 <@ usr$getTranscriptChallenge(_65);
      usr$z <- TMP346;
      _66 <- 4064;
      TMP347 <@ MStore(_66, usr$z);
      TMP347;
      _67 <- 67108864;
      TMP348 <@ usr$modexp(usr$z, _67);
      _68 <- TMP348;
      _69 <- 4192;
      TMP349 <@ MStore(_69, _68);
      TMP349;
      _70 <- 3072;
      TMP350 <@ MLoad(_70);
      _71 <- TMP350;
      TMP351 <@ usr$updateTranscript(_71);
      TMP351;
      _72 <- 2560;
      TMP352 <@ MLoad(_72);
      _73 <- TMP352;
      TMP353 <@ usr$updateTranscript(_73);
      TMP353;
      _74 <- 2592;
      TMP354 <@ MLoad(_74);
      _75 <- TMP354;
      TMP355 <@ usr$updateTranscript(_75);
      TMP355;
      _76 <- 2624;
      TMP356 <@ MLoad(_76);
      _77 <- TMP356;
      TMP357 <@ usr$updateTranscript(_77);
      TMP357;
      _78 <- 2656;
      TMP358 <@ MLoad(_78);
      _79 <- TMP358;
      TMP359 <@ usr$updateTranscript(_79);
      TMP359;
      _80 <- 2688;
      TMP360 <@ MLoad(_80);
      _81 <- TMP360;
      TMP361 <@ usr$updateTranscript(_81);
      TMP361;
      _82 <- 2720;
      TMP362 <@ MLoad(_82);
      _83 <- TMP362;
      TMP363 <@ usr$updateTranscript(_83);
      TMP363;
      _84 <- 2752;
      TMP364 <@ MLoad(_84);
      _85 <- TMP364;
      TMP365 <@ usr$updateTranscript(_85);
      TMP365;
      _86 <- 2784;
      TMP366 <@ MLoad(_86);
      _87 <- TMP366;
      TMP367 <@ usr$updateTranscript(_87);
      TMP367;
      _88 <- 2816;
      TMP368 <@ MLoad(_88);
      _89 <- TMP368;
      TMP369 <@ usr$updateTranscript(_89);
      TMP369;
      _90 <- 2848;
      TMP370 <@ MLoad(_90);
      _91 <- TMP370;
      TMP371 <@ usr$updateTranscript(_91);
      TMP371;
      _92 <- 2944;
      TMP372 <@ MLoad(_92);
      _93 <- TMP372;
      TMP373 <@ usr$updateTranscript(_93);
      TMP373;
      _94 <- 3008;
      TMP374 <@ MLoad(_94);
      _95 <- TMP374;
      TMP375 <@ usr$updateTranscript(_95);
      TMP375;
      _96 <- 3040;
      TMP376 <@ MLoad(_96);
      _97 <- TMP376;
      TMP377 <@ usr$updateTranscript(_97);
      TMP377;
      _98 <- 2880;
      TMP378 <@ MLoad(_98);
      _99 <- TMP378;
      TMP379 <@ usr$updateTranscript(_99);
      TMP379;
      _100 <- 2912;
      TMP380 <@ MLoad(_100);
      _101 <- TMP380;
      TMP381 <@ usr$updateTranscript(_101);
      TMP381;
      _102 <- 2976;
      TMP382 <@ MLoad(_102);
      _103 <- TMP382;
      TMP383 <@ usr$updateTranscript(_103);
      TMP383;
      _104 <- 3104;
      TMP384 <@ MLoad(_104);
      _105 <- TMP384;
      TMP385 <@ usr$updateTranscript(_105);
      TMP385;
      _106 <- 7;
      TMP386 <@ usr$getTranscriptChallenge(_106);
      _107 <- TMP386;
      _108 <- 4000;
      TMP387 <@ MStore(_108, _107);
      TMP387;
      _109 <- 3136;
      TMP388 <@ MLoad(_109);
      _110 <- TMP388;
      TMP389 <@ usr$updateTranscript(_110);
      TMP389;
      _111 <- 3168;
      TMP390 <@ MLoad(_111);
      _112 <- TMP390;
      TMP391 <@ usr$updateTranscript(_112);
      TMP391;
      _113 <- 3200;
      TMP392 <@ MLoad(_113);
      _114 <- TMP392;
      TMP393 <@ usr$updateTranscript(_114);
      TMP393;
      _115 <- 3232;
      TMP394 <@ MLoad(_115);
      _116 <- TMP394;
      TMP395 <@ usr$updateTranscript(_116);
      TMP395;
      _117 <- 8;
      TMP396 <@ usr$getTranscriptChallenge(_117);
      _118 <- TMP396;
      _119 <- 4032;
      TMP397 <@ MStore(_119, _118);
      TMP397;
      
      }
    }
  
  proc usr$prepareAggregatedCommitment(): unit = {
    var usr$aggregationChallenge, usr$firstDCoeff, usr$firstTCoeff, _1, _2, TMP541, _3, TMP542, _4, _5, TMP543, _6, TMP544, _7, usr$aggregatedOpeningAtZ, TMP545, _8, TMP546, _9, _10, _11, TMP547, _12, _13, TMP548, _14, _15, _16, TMP549, _17, _18, TMP550, _19, _20, TMP551, _21, TMP552, _22, _23, TMP553, _24, _25, _26, TMP554, _27, _28, TMP555, _29, _30, TMP556, _31, _32, TMP557, _33, TMP558, _34, _35, TMP559, _36, _37, _38, TMP560, _39, _40, TMP561, _41, TMP562, _42, TMP563, _43, _44, TMP564, _45, _46, _47, TMP565, usr$copyPermutationCoeff, _48, _49, TMP566, _50, _51, TMP567, usr$aggregatedOpeningAtZOmega, _52, _53, TMP568, _54, _55, TMP569, _56, _57, TMP570, _58, _59, TMP571, _60, _61, TMP572, _62, _63, TMP573, _64, TMP574, usr$u, TMP575, _65, TMP576, _66, TMP577, _67, TMP578, _68, usr$aggregatedValue, _69, _70, TMP579, _71, _72, TMP580, TMP581;
      {
      usr$aggregationChallenge <- 1;
      _1 <- 4288;
      TMP541 <@ MLoad(_1);
      _2 <- TMP541;
      _3 <- 4480;
      TMP542 <@ MStore(_3, _2);
      TMP542;
      _4 <- 4320;
      TMP543 <@ MLoad(_4);
      _5 <- TMP543;
      _6 <- 4512;
      TMP544 <@ MStore(_6, _5);
      TMP544;
      _7 <- 3072;
      TMP545 <@ MLoad(_7);
      usr$aggregatedOpeningAtZ <- TMP545;
      _8 <- 4352;
      TMP546 <@ usr$pointAddIntoDest(_3, _8, _3);
      TMP546;
      _9 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _10 <- 4000;
      TMP547 <@ MLoad(_10);
      _11 <- TMP547;
      usr$aggregationChallenge <- mulmod(usr$aggregationChallenge, _11, _9);
      _12 <- 3104;
      TMP548 <@ MLoad(_12);
      _13 <- TMP548;
      _14 <- mulmod(usr$aggregationChallenge, _13, _9);
      usr$aggregatedOpeningAtZ <- addmod(usr$aggregatedOpeningAtZ, _14, _9);
      _15 <- 2560;
      _16 <- 1856;
      TMP549 <@ usr$updateAggregationChallenge(_16, _15, usr$aggregationChallenge, usr$aggregatedOpeningAtZ);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- TMP549;
      _17 <- 2592;
      _18 <- 1920;
      TMP550 <@ usr$updateAggregationChallenge(_18, _17, usr$aggregationChallenge, usr$aggregatedOpeningAtZ);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- TMP550;
      _19 <- 2624;
      _20 <- 1984;
      TMP551 <@ usr$updateAggregationChallenge(_20, _19, usr$aggregationChallenge, usr$aggregatedOpeningAtZ);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- TMP551;
      TMP552 <@ MLoad(_10);
      _21 <- TMP552;
      usr$aggregationChallenge <- mulmod(usr$aggregationChallenge, _21, _9);
      usr$firstDCoeff <- usr$aggregationChallenge;
      _22 <- 2656;
      TMP553 <@ MLoad(_22);
      _23 <- TMP553;
      _24 <- mulmod(usr$aggregationChallenge, _23, _9);
      usr$aggregatedOpeningAtZ <- addmod(usr$aggregatedOpeningAtZ, _24, _9);
      _25 <- 2720;
      _26 <- 1024;
      TMP554 <@ usr$updateAggregationChallenge(_26, _25, usr$aggregationChallenge, usr$aggregatedOpeningAtZ);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- TMP554;
      _27 <- 2752;
      _28 <- 1152;
      TMP555 <@ usr$updateAggregationChallenge(_28, _27, usr$aggregationChallenge, usr$aggregatedOpeningAtZ);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- TMP555;
      _29 <- 2784;
      _30 <- 1216;
      TMP556 <@ usr$updateAggregationChallenge(_30, _29, usr$aggregationChallenge, usr$aggregatedOpeningAtZ);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- TMP556;
      _31 <- 2816;
      _32 <- 1280;
      TMP557 <@ usr$updateAggregationChallenge(_32, _31, usr$aggregationChallenge, usr$aggregatedOpeningAtZ);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- TMP557;
      TMP558 <@ MLoad(_10);
      _33 <- TMP558;
      usr$aggregationChallenge <- mulmod(usr$aggregationChallenge, _33, _9);
      usr$firstTCoeff <- usr$aggregationChallenge;
      _34 <- 2944;
      TMP559 <@ MLoad(_34);
      _35 <- TMP559;
      _36 <- mulmod(usr$aggregationChallenge, _35, _9);
      usr$aggregatedOpeningAtZ <- addmod(usr$aggregatedOpeningAtZ, _36, _9);
      _37 <- 3008;
      _38 <- 1408;
      TMP560 <@ usr$updateAggregationChallenge(_38, _37, usr$aggregationChallenge, usr$aggregatedOpeningAtZ);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- TMP560;
      _39 <- 3040;
      _40 <- 1728;
      TMP561 <@ usr$updateAggregationChallenge(_40, _39, usr$aggregationChallenge, usr$aggregatedOpeningAtZ);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- TMP561;
      _41 <- 4608;
      TMP562 <@ MStore(_41, usr$aggregatedOpeningAtZ);
      TMP562;
      TMP563 <@ MLoad(_10);
      _42 <- TMP563;
      usr$aggregationChallenge <- mulmod(usr$aggregationChallenge, _42, _9);
      _43 <- 4032;
      TMP564 <@ MLoad(_43);
      _44 <- TMP564;
      _45 <- mulmod(usr$aggregationChallenge, _44, _9);
      _46 <- 4928;
      TMP565 <@ MLoad(_46);
      _47 <- TMP565;
      usr$copyPermutationCoeff <- addmod(_47, _45, _9);
      _48 <- 4544;
      _49 <- 2112;
      TMP566 <@ usr$pointMulIntoDest(_49, usr$copyPermutationCoeff, _48);
      TMP566;
      _50 <- 2848;
      TMP567 <@ MLoad(_50);
      _51 <- TMP567;
      usr$aggregatedOpeningAtZOmega <- mulmod(_51, usr$aggregationChallenge, _9);
      _52 <- 2688;
      _53 <- 2048;
      TMP568 <@ usr$updateAggregationChallenge_105(_53, _52, usr$firstDCoeff, usr$aggregationChallenge, usr$aggregatedOpeningAtZOmega);
      usr$aggregationChallengeusr$aggregatedOpeningAtZOmega, <- TMP568;
      _54 <- 4992;
      TMP569 <@ MLoad(_54);
      _55 <- TMP569;
      _56 <- 2880;
      _57 <- 2176;
      TMP570 <@ usr$updateAggregationChallenge_105(_57, _56, _55, usr$aggregationChallenge, usr$aggregatedOpeningAtZOmega);
      usr$aggregationChallengeusr$aggregatedOpeningAtZOmega, <- TMP570;
      _58 <- 4960;
      TMP571 <@ MLoad(_58);
      _59 <- TMP571;
      _60 <- 2912;
      _61 <- 2240;
      TMP572 <@ usr$updateAggregationChallenge_105(_61, _60, _59, usr$aggregationChallenge, usr$aggregatedOpeningAtZOmega);
      usr$aggregationChallengeusr$aggregatedOpeningAtZOmega, <- TMP572;
      _62 <- 2976;
      _63 <- 4416;
      TMP573 <@ usr$updateAggregationChallenge_105(_63, _62, usr$firstTCoeff, usr$aggregationChallenge, usr$aggregatedOpeningAtZOmega);
      usr$aggregationChallengeusr$aggregatedOpeningAtZOmega, <- TMP573;
      _64 <- 4640;
      TMP574 <@ MStore(_64, usr$aggregatedOpeningAtZOmega);
      TMP574;
      TMP575 <@ MLoad(_43);
      usr$u <- TMP575;
      _65 <- 4736;
      TMP576 <@ usr$pointAddIntoDest(_3, _48, _65);
      TMP576;
      TMP577 <@ MLoad(_41);
      _66 <- TMP577;
      TMP578 <@ MLoad(_64);
      _67 <- TMP578;
      _68 <- mulmod(_67, usr$u, _9);
      usr$aggregatedValue <- addmod(_68, _66, _9);
      _69 <- 1;
      _70 <- 4672;
      TMP579 <@ MStore(_70, _69);
      TMP579;
      _71 <- 2;
      _72 <- 4704;
      TMP580 <@ MStore(_72, _71);
      TMP580;
      TMP581 <@ usr$pointMulIntoDest(_70, usr$aggregatedValue, _70);
      TMP581;
      
      }
    }
  
  proc usr$pointNegate(usr$point : uint256): unit = {
    var _1, _2, usr$pY, TMP166, _3, TMP168, _4, _5, TMP169, _6, _7, TMP170;
      {
      _1 <- 32;
      _2 <- usr$point + _1;
      TMP166 <@ MLoad(_2);
      usr$pY <- TMP166;
      TMP167 <- usr$pY;
      if (TMP167 = 0)
        {
        TMP168 <@ MLoad(usr$point);
        _3 <- TMP168;
        if (_3)
          {
          _4 <- "pointNegate: invalid point";
          _5 <- 26;
          TMP169 <@ usr$revertWithMessage(_5, _4);
          TMP169;
          
          }
        ;
        
        }
      
      else {
        _6 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
        _7 <- _6 - usr$pY;
        TMP170 <@ MStore(_2, _7);
        TMP170;
        
        }
      ;
      
      }
    }
  
  proc abi_encode_bool_to_bool(value : uint256, pos : uint256): unit = {
    var _1, TMP34, TMP35;
      {
      TMP34 <@ cleanup_bool(value);
      _1 <- TMP34;
      TMP35 <@ MStore(pos, _1);
      TMP35;
      
      }
    }
  
  proc abi_decode(headStart : uint256, dataEnd : uint256): unit = {
    var _1, _2, _3, TMP43;
      {
      _1 <- 0;
      _2 <- dataEnd - headStart;
      _3 <- slt(_2, _1);
      if (_3)
        {
        TMP43 <@ revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b();
        TMP43;
        
        }
      ;
      
      }
    }
  
  proc abi_encode_bool(headStart : uint256, value0 : uint256): uint256 = {
    var tail, _1, _2, _3, TMP36;
      {
      _1 <- 32;
      tail <- headStart + _1;
      _2 <- 0;
      _3 <- headStart + _2;
      TMP36 <@ abi_encode_bool_to_bool(value0, _3);
      TMP36;
      return tail;
      
      }
    }
  
  proc allocate_unbounded(): uint256 = {
    var memPtr, _1, TMP19;
      {
      _1 <- 64;
      TMP19 <@ MLoad(_1);
      memPtr <- TMP19;
      return memPtr;
      
      }
    }
  
  proc usr$modexp(usr$value : uint256, usr$power : uint256): uint256 = {
    var usr$res, _1, _2, TMP101, TMP102, _3, TMP103, _4, TMP104, _5, TMP105, _6, _7, TMP106, _8, _9, _10, TMP107, _11, TMP108, _12, _13, _14, TMP109, TMP110;
      {
      _1 <- 32;
      _2 <- 0;
      TMP101 <@ MStore(_2, _1);
      TMP101;
      TMP102 <@ MStore(_1, _1);
      TMP102;
      _3 <- 64;
      TMP103 <@ MStore(_3, _1);
      TMP103;
      _4 <- 96;
      TMP104 <@ MStore(_4, usr$value);
      TMP104;
      _5 <- 128;
      TMP105 <@ MStore(_5, usr$power);
      TMP105;
      _6 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _7 <- 160;
      TMP106 <@ MStore(_7, _6);
      TMP106;
      _8 <- 192;
      _9 <- 5;
      TMP107 <@ Gas();
      _10 <- TMP107;
      TMP108 <@ StaticCall(_10, _9, _2, _8, _2, _1);
      _11 <- TMP108;
      _12 <- iszero(_11);
      if (_12)
        {
        _13 <- "modexp precompile failed";
        _14 <- 24;
        TMP109 <@ usr$revertWithMessage(_14, _13);
        TMP109;
        
        }
      ;
      TMP110 <@ MLoad(_2);
      usr$res <- TMP110;
      return usr$res;
      
      }
    }
  
  proc abi_decode_array_uint256_dyn_calldata(offset : uint256, end : uint256): (uint256 * uint256) = {
    var arrayPos, length, _1, _2, _3, _4, TMP20, TMP21, _5, _6, TMP22, _7, _8, _9, _10, TMP23;
      {
      _1 <- 31;
      _2 <- offset + _1;
      _3 <- slt(_2, end);
      _4 <- iszero(_3);
      if (_4)
        {
        TMP20 <@ revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d();
        TMP20;
        
        }
      ;
      TMP21 <@ CallDataLoad(offset);
      length <- TMP21;
      _5 <- 18446744073709551615;
      _6 <- gt(length, _5);
      if (_6)
        {
        TMP22 <@ revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490();
        TMP22;
        
        }
      ;
      _7 <- 32;
      arrayPos <- offset + _7;
      _8 <- length * _7;
      _9 <- arrayPos + _8;
      _10 <- gt(_9, end);
      if (_10)
        {
        TMP23 <@ revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef();
        TMP23;
        
        }
      ;
      return (arrayPos, length);
      
      }
    }
  
  proc usr$finalPairing(): unit = {
    var _1, usr$u, TMP582, _2, usr$z, TMP583, _3, _4, _5, TMP584, usr$zOmega, _6, _7, TMP585, _8, TMP586, _9, _10, TMP587, _11, TMP588, _12, TMP589, _13, _14, TMP590, _15, TMP591, TMP592, TMP593, _16, _17, TMP594, usr$uu, _18, TMP595, _19, TMP596, _20, TMP597, _21, TMP598, _22, _23, TMP599, _24, TMP600, _25, _26, TMP601, _27, _28, TMP602, _29, _30, TMP603, _31, _32, TMP604, _33, TMP605, _34, TMP606, _35, TMP607, _36, TMP608, _37, _38, TMP609, _39, _40, TMP610, _41, _42, TMP611, _43, _44, TMP612, _45, _46, _47, TMP613, usr$success, TMP614, _48, _49, TMP615, _50, TMP616, _51, _52, _53, TMP617;
      {
      _1 <- 4032;
      TMP582 <@ MLoad(_1);
      usr$u <- TMP582;
      _2 <- 4064;
      TMP583 <@ MLoad(_2);
      usr$z <- TMP583;
      _3 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _4 <- 13446667982376394161563610564587413125564757801019538732601045199901075958935;
      TMP584 <@ MLoad(_2);
      _5 <- TMP584;
      usr$zOmega <- mulmod(_5, _4, _3);
      _6 <- 4672;
      _7 <- 4736;
      TMP585 <@ usr$pointSubAssign(_7, _6);
      TMP585;
      _8 <- 3136;
      TMP586 <@ usr$pointMulAndAddIntoDest(_8, usr$z, _7);
      TMP586;
      _9 <- mulmod(usr$zOmega, usr$u, _3);
      _10 <- 3200;
      TMP587 <@ usr$pointMulAndAddIntoDest(_10, _9, _7);
      TMP587;
      TMP588 <@ MLoad(_8);
      _11 <- TMP588;
      _12 <- 4864;
      TMP589 <@ MStore(_12, _11);
      TMP589;
      _13 <- 3168;
      TMP590 <@ MLoad(_13);
      _14 <- TMP590;
      _15 <- 4896;
      TMP591 <@ MStore(_15, _14);
      TMP591;
      TMP592 <@ usr$pointMulAndAddIntoDest(_10, usr$u, _12);
      TMP592;
      TMP593 <@ usr$pointNegate(_12);
      TMP593;
      _16 <- 1792;
      TMP594 <@ MLoad(_16);
      _17 <- TMP594;
      if (_17)
        {
        usr$uu <- mulmod(usr$u, usr$u, _3);
        _18 <- 3264;
        TMP595 <@ usr$pointMulAndAddIntoDest(_18, usr$uu, _7);
        TMP595;
        _19 <- 3328;
        TMP596 <@ usr$pointMulAndAddIntoDest(_19, usr$uu, _12);
        TMP596;
        
        }
      ;
      TMP597 <@ MLoad(_7);
      _20 <- TMP597;
      _21 <- 0;
      TMP598 <@ MStore(_21, _20);
      TMP598;
      _22 <- 4768;
      TMP599 <@ MLoad(_22);
      _23 <- TMP599;
      _24 <- 32;
      TMP600 <@ MStore(_24, _23);
      TMP600;
      _25 <- 11559732032986387107991004021392285783925812861821192530917403151452391805634;
      _26 <- 64;
      TMP601 <@ MStore(_26, _25);
      TMP601;
      _27 <- 10857046999023057135944570762232829481370756359578518086990519993285655852781;
      _28 <- 96;
      TMP602 <@ MStore(_28, _27);
      TMP602;
      _29 <- 4082367875863433681332203403145435568316851327593401208105741076214120093531;
      _30 <- 128;
      TMP603 <@ MStore(_30, _29);
      TMP603;
      _31 <- 8495653923123431417604973247489272438418190587263600148770280649306958101930;
      _32 <- 160;
      TMP604 <@ MStore(_32, _31);
      TMP604;
      TMP605 <@ MLoad(_12);
      _33 <- TMP605;
      _34 <- 192;
      TMP606 <@ MStore(_34, _33);
      TMP606;
      TMP607 <@ MLoad(_15);
      _35 <- TMP607;
      _36 <- 224;
      TMP608 <@ MStore(_36, _35);
      TMP608;
      _37 <- 17212635814319756364507010169094758005397460366678210664966334781961899574209;
      _38 <- 256;
      TMP609 <@ MStore(_38, _37);
      TMP609;
      _39 <- 496075682290949347282619629729389528669750910289829251317610107342504362928;
      _40 <- 288;
      TMP610 <@ MStore(_40, _39);
      TMP610;
      _41 <- 2255182984359105691812395885056400739448730162863181907784180250290003009508;
      _42 <- 320;
      TMP611 <@ MStore(_42, _41);
      TMP611;
      _43 <- 15828724851114720558251891430452666121603726704878231219287131634746610441813;
      _44 <- 352;
      TMP612 <@ MStore(_44, _43);
      TMP612;
      _45 <- 384;
      _46 <- 8;
      TMP613 <@ Gas();
      _47 <- TMP613;
      TMP614 <@ StaticCall(_47, _46, _21, _45, _21, _24);
      usr$success <- TMP614;
      _48 <- iszero(usr$success);
      if (_48)
        {
        _49 <- "finalPairing: precompile failure";
        TMP615 <@ usr$revertWithMessage(_24, _49);
        TMP615;
        
        }
      ;
      TMP616 <@ MLoad(_21);
      _50 <- TMP616;
      _51 <- iszero(_50);
      if (_51)
        {
        _52 <- "finalPairing: pairing failure";
        _53 <- 29;
        TMP617 <@ usr$revertWithMessage(_53, _52);
        TMP617;
        
        }
      ;
      
      }
    }
  
  proc constructor_IVerifier(): unit = {
      {
      
      }
    }
  
  proc BODY(): unit = {
      {
      TMP0 <@ MemoryGuard(128);
      _1 <- TMP0;
      _2 <- 64;
      TMP1 <@ MStore(_2, _1);
      TMP1;
      TMP2 <@ CallValue();
      _3 <- TMP2;
      if (_3)
        {
        TMP3 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb();
        TMP3;
        
        }
      ;
      TMP4 <@ constructor_Verifier();
      TMP4;
      TMP5 <@ allocate_unbounded();
      _4 <- TMP5;
      TMP6 <@ DataSize("Verifier_1261_deployed");
      _5 <- TMP6;
      TMP7 <@ DataOffset("Verifier_1261_deployed");
      _6 <- TMP7;
      TMP8 <@ CodeCopy(_4, _6, _5);
      TMP8;
      _7 <- _5;
      return (_4, _5);
      
      }
    }
  
  proc revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc usr$pointMulIntoDest(usr$point : uint256, usr$s : uint256, usr$dest : uint256): unit = {
    var _1, TMP111, _2, TMP112, _3, _4, _5, TMP113, TMP114, _6, TMP115, _7, _8, _9, TMP116, _10, TMP117, _11, _12, _13, TMP118;
      {
      TMP111 <@ MLoad(usr$point);
      _1 <- TMP111;
      _2 <- 0;
      TMP112 <@ MStore(_2, _1);
      TMP112;
      _3 <- 32;
      _4 <- usr$point + _3;
      TMP113 <@ MLoad(_4);
      _5 <- TMP113;
      TMP114 <@ MStore(_3, _5);
      TMP114;
      _6 <- 64;
      TMP115 <@ MStore(_6, usr$s);
      TMP115;
      _7 <- 96;
      _8 <- 7;
      TMP116 <@ Gas();
      _9 <- TMP116;
      TMP117 <@ StaticCall(_9, _8, _2, _7, usr$dest, _6);
      _10 <- TMP117;
      _11 <- iszero(_10);
      if (_11)
        {
        _12 <- "pointMulIntoDest: ecMul failed";
        _13 <- 30;
        TMP118 <@ usr$revertWithMessage(_13, _12);
        TMP118;
        
        }
      ;
      
      }
    }
  
  proc usr$evaluateLagrangePolyOutOfDomain(usr$polyNum : uint256, usr$at : uint256): uint256 = {
    var usr$res, usr$omegaPower, _1, TMP420, _2, _3, _4, _5, _6, TMP421, _7, _8, _9, TMP422, _10, usr$denominator, _11, _12, TMP423;
      {
      usr$omegaPower <- 1;
      if (usr$polyNum)
        {
        _1 <- 13446667982376394161563610564587413125564757801019538732601045199901075958935;
        TMP420 <@ usr$modexp(_1, usr$polyNum);
        usr$omegaPower <- TMP420;
        
        }
      ;
      _2 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _3 <- 1;
      _4 <- _2 - _3;
      _5 <- 67108864;
      TMP421 <@ usr$modexp(usr$at, _5);
      _6 <- TMP421;
      usr$res <- addmod(_6, _4, _2);
      _7 <- iszero(usr$res);
      if (_7)
        {
        _8 <- "invalid vanishing polynomial";
        _9 <- 28;
        TMP422 <@ usr$revertWithMessage(_9, _8);
        TMP422;
        
        }
      ;
      usr$res <- mulmod(usr$res, usr$omegaPower, _2);
      _10 <- _2 - usr$omegaPower;
      usr$denominator <- addmod(usr$at, _10, _2);
      usr$denominator <- mulmod(usr$denominator, _5, _2);
      _11 <- 2;
      _12 <- _2 - _11;
      TMP423 <@ usr$modexp(usr$denominator, _12);
      usr$denominator <- TMP423;
      usr$res <- mulmod(usr$res, usr$denominator, _2);
      return usr$res;
      
      }
    }
  
  proc fun_verificationKeyHash(): uint256 = {
    var var_vkHash, TMP53, TMP54, usr$start, usr$end, _1, _2, usr$length, TMP55;
      {
      TMP53 <@ Pop(zero_value_for_split_bytes32);
      TMP53;
      TMP54 <@ fun_loadVerificationKey();
      TMP54;
      usr$start <- 512;
      usr$end <- 1792;
      _1 <- 32;
      _2 <- usr$end - usr$start;
      usr$length <- _2 + _1;
      TMP55 <@ Keccak256(usr$start, usr$length);
      var_vkHash <- TMP55;
      return var_vkHash;
      
      }
    }
  
  proc usr$addAssignRescueCustomGateLinearisationContributionWithV(usr$dest : uint256, usr$stateOpening0AtZ : uint256, usr$stateOpening1AtZ : uint256, usr$stateOpening2AtZ : uint256, usr$stateOpening3AtZ : uint256): unit = {
    var usr$accumulator, usr$intermediateValue, _1, _2, _3, _4, TMP464, _5, _6, _7, TMP465, _8, _9, _10, TMP466, _11, _12, TMP467, _13, TMP468;
      {
      _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      usr$accumulator <- mulmod(usr$stateOpening0AtZ, usr$stateOpening0AtZ, _1);
      _2 <- _1 - usr$stateOpening1AtZ;
      usr$accumulator <- addmod(usr$accumulator, _2, _1);
      _3 <- 3520;
      TMP464 <@ MLoad(_3);
      _4 <- TMP464;
      usr$accumulator <- mulmod(usr$accumulator, _4, _1);
      usr$intermediateValue <- mulmod(usr$stateOpening1AtZ, usr$stateOpening1AtZ, _1);
      _5 <- _1 - usr$stateOpening2AtZ;
      usr$intermediateValue <- addmod(usr$intermediateValue, _5, _1);
      _6 <- 3616;
      TMP465 <@ MLoad(_6);
      _7 <- TMP465;
      usr$intermediateValue <- mulmod(usr$intermediateValue, _7, _1);
      usr$accumulator <- addmod(usr$accumulator, usr$intermediateValue, _1);
      usr$intermediateValue <- mulmod(usr$stateOpening2AtZ, usr$stateOpening0AtZ, _1);
      _8 <- _1 - usr$stateOpening3AtZ;
      usr$intermediateValue <- addmod(usr$intermediateValue, _8, _1);
      _9 <- 3648;
      TMP466 <@ MLoad(_9);
      _10 <- TMP466;
      usr$intermediateValue <- mulmod(usr$intermediateValue, _10, _1);
      usr$accumulator <- addmod(usr$accumulator, usr$intermediateValue, _1);
      _11 <- 4000;
      TMP467 <@ MLoad(_11);
      _12 <- TMP467;
      usr$accumulator <- mulmod(usr$accumulator, _12, _1);
      _13 <- 1088;
      TMP468 <@ usr$pointMulAndAddIntoDest(_13, usr$accumulator, usr$dest);
      TMP468;
      
      }
    }
  
  proc usr$updateAggregationChallenge(usr$queriesCommitmentPoint : uint256, usr$valueAtZ : uint256, usr$curAggregationChallenge : uint256, usr$curAggregatedOpeningAtZ : uint256): (uint256 * uint256) = {
    var usr$newAggregationChallenge, usr$newAggregatedOpeningAtZ, _1, _2, _3, TMP534, _4, TMP535, _5, TMP536, _6;
      {
      _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _2 <- 4000;
      TMP534 <@ MLoad(_2);
      _3 <- TMP534;
      usr$newAggregationChallenge <- mulmod(usr$curAggregationChallenge, _3, _1);
      _4 <- 4480;
      TMP535 <@ usr$pointMulAndAddIntoDest(usr$queriesCommitmentPoint, usr$newAggregationChallenge, _4);
      TMP535;
      TMP536 <@ MLoad(usr$valueAtZ);
      _5 <- TMP536;
      _6 <- mulmod(usr$newAggregationChallenge, _5, _1);
      usr$newAggregatedOpeningAtZ <- addmod(usr$curAggregatedOpeningAtZ, _6, _1);
      return (usr$newAggregationChallenge, usr$newAggregatedOpeningAtZ);
      
      }
    }
  
  proc cleanup_bool(value : uint256): uint256 = {
    var cleaned, _1;
      {
      _1 <- iszero(value);
      cleaned <- iszero(_1);
      return cleaned;
      
      }
    }
  
  proc abi_decode_array_uint256_dyn_calldatat_array_uint256_dyn_calldatat_array_uint256_dyn_calldata(headStart : uint256, dataEnd : uint256): (uint256 * uint256 * uint256 * uint256 * uint256 * uint256) = {
    var value0, value1, value2, value3, value4, value5, _1, _2, _3, TMP24, _4, _5, offset, TMP25, _6, _7, TMP26, _8, TMP27, _9, _10, offset_1, TMP28, _11, TMP29, _12, TMP30, _13, _14, offset_2, TMP31, _15, TMP32, _16, TMP33;
      {
      _1 <- 96;
      _2 <- dataEnd - headStart;
      _3 <- slt(_2, _1);
      if (_3)
        {
        TMP24 <@ revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b();
        TMP24;
        
        }
      ;
      _4 <- 0;
      _5 <- headStart + _4;
      TMP25 <@ CallDataLoad(_5);
      offset <- TMP25;
      _6 <- 18446744073709551615;
      _7 <- gt(offset, _6);
      if (_7)
        {
        TMP26 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
        TMP26;
        
        }
      ;
      _8 <- headStart + offset;
      TMP27 <@ abi_decode_array_uint256_dyn_calldata(_8, dataEnd);
      value0value1, <- TMP27;
      _9 <- 32;
      _10 <- headStart + _9;
      TMP28 <@ CallDataLoad(_10);
      offset_1 <- TMP28;
      _11 <- gt(offset_1, _6);
      if (_11)
        {
        TMP29 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
        TMP29;
        
        }
      ;
      _12 <- headStart + offset_1;
      TMP30 <@ abi_decode_array_uint256_dyn_calldata(_12, dataEnd);
      value2value3, <- TMP30;
      _13 <- 64;
      _14 <- headStart + _13;
      TMP31 <@ CallDataLoad(_14);
      offset_2 <- TMP31;
      _15 <- gt(offset_2, _6);
      if (_15)
        {
        TMP32 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
        TMP32;
        
        }
      ;
      _16 <- headStart + offset_2;
      TMP33 <@ abi_decode_array_uint256_dyn_calldata(_16, dataEnd);
      value4value5, <- TMP33;
      return (value0, value1, value2, value3, value4, value5);
      
      }
    }
  
  proc revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(): unit = {
    var _1, _2;
      {
      _1 <- 0;
      _2 <- _1;
      return ();
      
      }
    }
  
  proc usr$lookupQuotientContribution(): uint256 = {
    var usr$res, _1, usr$betaLookup, TMP437, _2, usr$gammaLookup, TMP438, _3, _4, usr$betaPlusOne, usr$betaGamma, _5, TMP439, _6, TMP440, _7, _8, TMP441, _9, _10, TMP442, _11, _12, TMP443, _13, _14, _15, usr$lastOmega, TMP444, _16, _17, _18, TMP445, usr$zMinusLastOmega, _19, TMP446, _20, _21, TMP447, _22, _23, TMP448, usr$intermediateValue, _24, _25, usr$lnMinusOneAtZ, TMP449, usr$betaGammaPowered, TMP450, _26, usr$alphaPower8, TMP451, _27, usr$subtrahend, _28;
      {
      _1 <- 3872;
      TMP437 <@ MLoad(_1);
      usr$betaLookup <- TMP437;
      _2 <- 3904;
      TMP438 <@ MLoad(_2);
      usr$gammaLookup <- TMP438;
      _3 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _4 <- 1;
      usr$betaPlusOne <- addmod(usr$betaLookup, _4, _3);
      usr$betaGamma <- mulmod(usr$betaPlusOne, usr$gammaLookup, _3);
      _5 <- 3936;
      TMP439 <@ MStore(_5, usr$betaPlusOne);
      TMP439;
      _6 <- 3968;
      TMP440 <@ MStore(_6, usr$betaGamma);
      TMP440;
      _7 <- 2880;
      TMP441 <@ MLoad(_7);
      _8 <- TMP441;
      usr$res <- mulmod(_8, usr$betaLookup, _3);
      usr$res <- addmod(usr$res, usr$betaGamma, _3);
      _9 <- 2912;
      TMP442 <@ MLoad(_9);
      _10 <- TMP442;
      usr$res <- mulmod(usr$res, _10, _3);
      _11 <- 3744;
      TMP443 <@ MLoad(_11);
      _12 <- TMP443;
      usr$res <- mulmod(usr$res, _12, _3);
      _13 <- 67108864;
      _14 <- _13 - _4;
      _15 <- 13446667982376394161563610564587413125564757801019538732601045199901075958935;
      TMP444 <@ usr$modexp(_15, _14);
      usr$lastOmega <- TMP444;
      _16 <- _3 - usr$lastOmega;
      _17 <- 4064;
      TMP445 <@ MLoad(_17);
      _18 <- TMP445;
      usr$zMinusLastOmega <- addmod(_18, _16, _3);
      _19 <- 4096;
      TMP446 <@ MStore(_19, usr$zMinusLastOmega);
      TMP446;
      usr$res <- mulmod(usr$res, usr$zMinusLastOmega, _3);
      _20 <- 3776;
      TMP447 <@ MLoad(_20);
      _21 <- TMP447;
      _22 <- 4128;
      TMP448 <@ MLoad(_22);
      _23 <- TMP448;
      usr$intermediateValue <- mulmod(_23, _21, _3);
      _24 <- _3 - usr$intermediateValue;
      usr$res <- addmod(usr$res, _24, _3);
      _25 <- 4160;
      TMP449 <@ MLoad(_25);
      usr$lnMinusOneAtZ <- TMP449;
      TMP450 <@ usr$modexp(usr$betaGamma, _14);
      usr$betaGammaPowered <- TMP450;
      _26 <- 3808;
      TMP451 <@ MLoad(_26);
      usr$alphaPower8 <- TMP451;
      _27 <- mulmod(usr$lnMinusOneAtZ, usr$betaGammaPowered, _3);
      usr$subtrahend <- mulmod(_27, usr$alphaPower8, _3);
      _28 <- _3 - usr$subtrahend;
      usr$res <- addmod(usr$res, _28, _3);
      return usr$res;
      
      }
    }
  
  proc revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc external_fun_verify(): unit = {
    var _1, TMP37, TMP38, _2, TMP39, _3, param, param_1, param_2, param_3, param_4, param_5, TMP40, TMP41, TMP42;
      {
      TMP37 <@ CallValue();
      _1 <- TMP37;
      if (_1)
        {
        TMP38 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb();
        TMP38;
        
        }
      ;
      TMP39 <@ CallDataSize();
      _2 <- TMP39;
      _3 <- 4;
      TMP40 <@ abi_decode_array_uint256_dyn_calldatat_array_uint256_dyn_calldatat_array_uint256_dyn_calldata(_3, _2);
      paramparam_1,param_2,param_3,param_4,param_5, <- TMP40;
      TMP41 <@ fun_verify(param, param_1, param_2, param_3, param_4, param_5);
      TMP42 <@ Pop(TMP41);
      TMP42;
      
      }
    }
  
  proc usr$mainGateLinearisationContributionWithV(usr$dest : uint256, usr$stateOpening0AtZ : uint256, usr$stateOpening1AtZ : uint256, usr$stateOpening2AtZ : uint256, usr$stateOpening3AtZ : uint256): unit = {
    var _1, TMP452, _2, TMP453, _3, TMP454, _4, TMP455, _5, _6, _7, TMP456, _8, _9, TMP457, _10, TMP458, _11, _12, TMP459, _13, TMP460, _14, _15, TMP461, _16, _17, TMP462, usr$coeff, TMP463;
      {
      _1 <- 512;
      TMP452 <@ usr$pointMulIntoDest(_1, usr$stateOpening0AtZ, usr$dest);
      TMP452;
      _2 <- 576;
      TMP453 <@ usr$pointMulAndAddIntoDest(_2, usr$stateOpening1AtZ, usr$dest);
      TMP453;
      _3 <- 640;
      TMP454 <@ usr$pointMulAndAddIntoDest(_3, usr$stateOpening2AtZ, usr$dest);
      TMP454;
      _4 <- 704;
      TMP455 <@ usr$pointMulAndAddIntoDest(_4, usr$stateOpening3AtZ, usr$dest);
      TMP455;
      _5 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _6 <- mulmod(usr$stateOpening0AtZ, usr$stateOpening1AtZ, _5);
      _7 <- 768;
      TMP456 <@ usr$pointMulAndAddIntoDest(_7, _6, usr$dest);
      TMP456;
      _8 <- mulmod(usr$stateOpening0AtZ, usr$stateOpening2AtZ, _5);
      _9 <- 832;
      TMP457 <@ usr$pointMulAndAddIntoDest(_9, _8, usr$dest);
      TMP457;
      _10 <- 896;
      TMP458 <@ usr$pointAddAssign(usr$dest, _10);
      TMP458;
      _11 <- 2688;
      TMP459 <@ MLoad(_11);
      _12 <- TMP459;
      _13 <- 960;
      TMP460 <@ usr$pointMulAndAddIntoDest(_13, _12, usr$dest);
      TMP460;
      _14 <- 4000;
      TMP461 <@ MLoad(_14);
      _15 <- TMP461;
      _16 <- 2720;
      TMP462 <@ MLoad(_16);
      _17 <- TMP462;
      usr$coeff <- mulmod(_17, _15, _5);
      TMP463 <@ usr$pointMulIntoDest(usr$dest, usr$coeff, usr$dest);
      TMP463;
      
      }
    }
  
  proc usr$pointAddAssign(usr$p1 : uint256, usr$p2 : uint256): unit = {
    var _1, TMP141, _2, TMP142, _3, _4, _5, TMP143, TMP144, _6, TMP145, _7, TMP146, _8, _9, TMP147, _10, TMP148, _11, _12, _13, TMP149, _14, TMP150, _15, _16, _17, TMP151;
      {
      TMP141 <@ MLoad(usr$p1);
      _1 <- TMP141;
      _2 <- 0;
      TMP142 <@ MStore(_2, _1);
      TMP142;
      _3 <- 32;
      _4 <- usr$p1 + _3;
      TMP143 <@ MLoad(_4);
      _5 <- TMP143;
      TMP144 <@ MStore(_3, _5);
      TMP144;
      TMP145 <@ MLoad(usr$p2);
      _6 <- TMP145;
      _7 <- 64;
      TMP146 <@ MStore(_7, _6);
      TMP146;
      _8 <- usr$p2 + _3;
      TMP147 <@ MLoad(_8);
      _9 <- TMP147;
      _10 <- 96;
      TMP148 <@ MStore(_10, _9);
      TMP148;
      _11 <- 128;
      _12 <- 6;
      TMP149 <@ Gas();
      _13 <- TMP149;
      TMP150 <@ StaticCall(_13, _12, _2, _11, usr$p1, _7);
      _14 <- TMP150;
      _15 <- iszero(_14);
      if (_15)
        {
        _16 <- "pointAddAssign: ecAdd failed";
        _17 <- 28;
        TMP151 <@ usr$revertWithMessage(_17, _16);
        TMP151;
        
        }
      ;
      
      }
    }
  
  proc usr$permutationQuotientContribution(): uint256 = {
    var usr$res, _1, _2, _3, TMP424, _4, _5, TMP425, _6, usr$gamma, TMP426, _7, usr$beta, TMP427, usr$factorMultiplier, _8, _9, TMP428, _10, _11, TMP429, _12, _13, TMP430, _14, _15, TMP431, _16, _17, TMP432, _18, _19, TMP433, _20, _21, TMP434, _22, _23, usr$l0AtZ, TMP435, _24, _25, TMP436, _26;
      {
      _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _2 <- 2848;
      TMP424 <@ MLoad(_2);
      _3 <- TMP424;
      _4 <- 3680;
      TMP425 <@ MLoad(_4);
      _5 <- TMP425;
      usr$res <- mulmod(_5, _3, _1);
      _6 <- 3584;
      TMP426 <@ MLoad(_6);
      usr$gamma <- TMP426;
      _7 <- 3552;
      TMP427 <@ MLoad(_7);
      usr$beta <- TMP427;
      _8 <- 2752;
      TMP428 <@ MLoad(_8);
      _9 <- TMP428;
      usr$factorMultiplier <- mulmod(_9, usr$beta, _1);
      usr$factorMultiplier <- addmod(usr$factorMultiplier, usr$gamma, _1);
      _10 <- 2560;
      TMP429 <@ MLoad(_10);
      _11 <- TMP429;
      usr$factorMultiplier <- addmod(usr$factorMultiplier, _11, _1);
      usr$res <- mulmod(usr$res, usr$factorMultiplier, _1);
      _12 <- 2784;
      TMP430 <@ MLoad(_12);
      _13 <- TMP430;
      usr$factorMultiplier <- mulmod(_13, usr$beta, _1);
      usr$factorMultiplier <- addmod(usr$factorMultiplier, usr$gamma, _1);
      _14 <- 2592;
      TMP431 <@ MLoad(_14);
      _15 <- TMP431;
      usr$factorMultiplier <- addmod(usr$factorMultiplier, _15, _1);
      usr$res <- mulmod(usr$res, usr$factorMultiplier, _1);
      _16 <- 2816;
      TMP432 <@ MLoad(_16);
      _17 <- TMP432;
      usr$factorMultiplier <- mulmod(_17, usr$beta, _1);
      usr$factorMultiplier <- addmod(usr$factorMultiplier, usr$gamma, _1);
      _18 <- 2624;
      TMP433 <@ MLoad(_18);
      _19 <- TMP433;
      usr$factorMultiplier <- addmod(usr$factorMultiplier, _19, _1);
      usr$res <- mulmod(usr$res, usr$factorMultiplier, _1);
      _20 <- 2656;
      TMP434 <@ MLoad(_20);
      _21 <- TMP434;
      _22 <- addmod(_21, usr$gamma, _1);
      usr$res <- mulmod(usr$res, _22, _1);
      usr$res <- _1 - usr$res;
      _23 <- 4128;
      TMP435 <@ MLoad(_23);
      usr$l0AtZ <- TMP435;
      _24 <- 3712;
      TMP436 <@ MLoad(_24);
      _25 <- TMP436;
      usr$l0AtZ <- mulmod(usr$l0AtZ, _25, _1);
      _26 <- _1 - usr$l0AtZ;
      usr$res <- addmod(usr$res, _26, _1);
      return usr$res;
      
      }
    }
  
  proc external_fun_verificationKeyHash(): unit = {
    var _1, TMP46, TMP47, _2, TMP48, _3, TMP49, ret, TMP50, memPos, TMP51, memEnd, TMP52, _4;
      {
      TMP46 <@ CallValue();
      _1 <- TMP46;
      if (_1)
        {
        TMP47 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb();
        TMP47;
        
        }
      ;
      TMP48 <@ CallDataSize();
      _2 <- TMP48;
      _3 <- 4;
      TMP49 <@ abi_decode(_3, _2);
      TMP49;
      TMP50 <@ fun_verificationKeyHash();
      ret <- TMP50;
      TMP51 <@ allocate_unbounded();
      memPos <- TMP51;
      TMP52 <@ abi_encode_bytes32(memPos, ret);
      memEnd <- TMP52;
      _4 <- memEnd - memPos;
      return (memPos, _4);
      
      }
    }
  
  proc BODY(): unit = {
    var zero_bool, TMP618, TMP619, TMP620, TMP621, TMP622, TMP623, TMP624, _1, _2, TMP625, _3;
      {
      _1 <- 128;
      _2 <- 64;
      TMP11 <@ MStore(_2, _1);
      TMP11;
      _3 <- 4;
      TMP12 <@ CallDataSize();
      _4 <- TMP12;
      _5 <- lt(_4, _3);
      _6 <- iszero(_5);
      if (_6)
        {
        _7 <- 0;
        TMP13 <@ CallDataLoad(_7);
        _8 <- TMP13;
        TMP14 <@ shift_right_unsigned(_8);
        selector <- TMP14;
        TMP15 <- selector;
        if (TMP15 = 2279198755)
          {
          TMP16 <@ external_fun_verify();
          TMP16;
          
          }
        
        else {
          if (TMP15 = 2659796434)
            {
            TMP17 <@ external_fun_verificationKeyHash();
            TMP17;
            
            }
          ;
          
          }
        ;
        
        }
      ;
      TMP18 <@ revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74();
      TMP18;
      
      }
    }
  
  proc allocate_unbounded(): uint256 = {
    var memPtr, _1, TMP9;
      {
      _1 <- 64;
      TMP9 <@ MLoad(_1);
      memPtr <- TMP9;
      return memPtr;
      
      }
    }
  
  proc usr$revertWithMessage(usr$len : uint256, usr$reason : uint256): unit = {
    var _1, _2, TMP97, _3, _4, TMP98, _5, TMP99, _6, TMP100, _7;
      {
      _1 <- 229 << 4594637;
      _2 <- 0;
      TMP97 <@ MStore(_2, _1);
      TMP97;
      _3 <- 32;
      _4 <- 4;
      TMP98 <@ MStore(_4, _3);
      TMP98;
      _5 <- 36;
      TMP99 <@ MStore(_5, usr$len);
      TMP99;
      _6 <- 68;
      TMP100 <@ MStore(_6, usr$reason);
      TMP100;
      _7 <- 100;
      return ();
      
      }
    }
  
  proc usr$updateTranscript(usr$value : uint256): unit = {
    var _1, _2, TMP171, _3, TMP172, _4, _5, usr$newState0, TMP173, _6, TMP174, usr$newState1, TMP175, _7, TMP176, _8, TMP177;
      {
      _1 <- 0;
      _2 <- 3395;
      TMP171 <@ MStore8(_2, _1);
      TMP171;
      _3 <- 3460;
      TMP172 <@ MStore(_3, usr$value);
      TMP172;
      _4 <- 100;
      _5 <- 3392;
      TMP173 <@ Keccak256(_5, _4);
      usr$newState0 <- TMP173;
      _6 <- 1;
      TMP174 <@ MStore8(_2, _6);
      TMP174;
      TMP175 <@ Keccak256(_5, _4);
      usr$newState1 <- TMP175;
      _7 <- 3428;
      TMP176 <@ MStore(_7, usr$newState1);
      TMP176;
      _8 <- 3396;
      TMP177 <@ MStore(_8, usr$newState0);
      TMP177;
      
      }
    }
  
  proc usr$pointSubAssign(usr$p1 : uint256, usr$p2 : uint256): unit = {
    var _1, TMP130, _2, TMP131, _3, _4, _5, TMP132, TMP133, _6, TMP134, _7, TMP135, _8, _9, TMP136, _10, _11, _12, TMP137, _13, _14, _15, TMP138, _16, TMP139, _17, _18, _19, TMP140;
      {
      TMP130 <@ MLoad(usr$p1);
      _1 <- TMP130;
      _2 <- 0;
      TMP131 <@ MStore(_2, _1);
      TMP131;
      _3 <- 32;
      _4 <- usr$p1 + _3;
      TMP132 <@ MLoad(_4);
      _5 <- TMP132;
      TMP133 <@ MStore(_3, _5);
      TMP133;
      TMP134 <@ MLoad(usr$p2);
      _6 <- TMP134;
      _7 <- 64;
      TMP135 <@ MStore(_7, _6);
      TMP135;
      _8 <- usr$p2 + _3;
      TMP136 <@ MLoad(_8);
      _9 <- TMP136;
      _10 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
      _11 <- _10 - _9;
      _12 <- 96;
      TMP137 <@ MStore(_12, _11);
      TMP137;
      _13 <- 128;
      _14 <- 6;
      TMP138 <@ Gas();
      _15 <- TMP138;
      TMP139 <@ StaticCall(_15, _14, _2, _13, usr$p1, _7);
      _16 <- TMP139;
      _17 <- iszero(_16);
      if (_17)
        {
        _18 <- "pointSubAssign: ecAdd failed";
        _19 <- 28;
        TMP140 <@ usr$revertWithMessage(_19, _18);
        TMP140;
        
        }
      ;
      
      }
    }
  
  proc revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc usr$loadProof(): unit = {
    var _1, usr$offset, TMP181, _2, usr$publicInputLengthInWords, TMP182, _3, usr$isValid, _4, _5, _6, _7, TMP183, _8, _9, TMP184, TMP185, _10, usr$proofLengthInWords, TMP186, _11, _12, _13, _14, _15, TMP187, usr$x, _16, _17, _18, TMP188, usr$y, usr$xx, _19, _20, _21, _22, _23, _24, TMP189, _25, TMP190, _26, _27, _28, TMP191, usr$x_1, _29, _30, _31, TMP192, usr$y_1, usr$xx_1, _32, _33, _34, _35, _36, TMP193, _37, TMP194, _38, _39, _40, TMP195, usr$x_2, _41, _42, _43, TMP196, usr$y_2, usr$xx_2, _44, _45, _46, _47, _48, TMP197, _49, TMP198, _50, _51, _52, TMP199, usr$x_3, _53, _54, _55, TMP200, usr$y_3, usr$xx_3, _56, _57, _58, _59, _60, TMP201, _61, TMP202, _62, _63, _64, TMP203, usr$x_4, _65, _66, _67, TMP204, usr$y_4, usr$xx_4, _68, _69, _70, _71, _72, TMP205, _73, TMP206, _74, _75, _76, TMP207, usr$x_5, _77, _78, _79, TMP208, usr$y_5, usr$xx_5, _80, _81, _82, _83, _84, TMP209, _85, TMP210, _86, _87, _88, TMP211, usr$x_6, _89, _90, _91, TMP212, usr$y_6, usr$xx_6, _92, _93, _94, _95, _96, TMP213, _97, TMP214, _98, _99, _100, TMP215, usr$x_7, _101, _102, _103, TMP216, usr$y_7, usr$xx_7, _104, _105, _106, _107, _108, TMP217, _109, TMP218, _110, _111, _112, TMP219, usr$x_8, _113, _114, _115, TMP220, usr$y_8, usr$xx_8, _116, _117, _118, _119, _120, TMP221, _121, TMP222, _122, _123, _124, TMP223, usr$x_9, _125, _126, _127, TMP224, usr$y_9, usr$xx_9, _128, _129, _130, _131, _132, TMP225, _133, TMP226, _134, _135, _136, TMP227, usr$x_10, _137, _138, _139, TMP228, usr$y_10, usr$xx_10, _140, _141, _142, _143, _144, TMP229, _145, TMP230, _146, _147, _148, _149, TMP231, _150, _151, TMP232, _152, _153, _154, TMP233, _155, _156, TMP234, _157, _158, _159, TMP235, _160, _161, TMP236, _162, _163, _164, TMP237, _165, _166, TMP238, _167, _168, _169, TMP239, _170, _171, TMP240, _172, _173, _174, TMP241, _175, _176, TMP242, _177, _178, _179, TMP243, _180, _181, TMP244, _182, _183, _184, TMP245, _185, _186, TMP246, _187, _188, _189, TMP247, _190, _191, TMP248, _192, _193, _194, TMP249, _195, _196, TMP250, _197, _198, _199, TMP251, _200, _201, TMP252, _202, _203, _204, TMP253, _205, _206, TMP254, _207, _208, _209, TMP255, _210, _211, TMP256, _212, _213, _214, TMP257, _215, _216, TMP258, _217, _218, _219, TMP259, _220, _221, TMP260, _222, _223, _224, TMP261, _225, _226, TMP262, _227, _228, _229, TMP263, _230, _231, TMP264, _232, _233, _234, TMP265, _235, _236, TMP266, _237, _238, _239, TMP267, usr$x_11, _240, _241, _242, TMP268, usr$y_11, usr$xx_11, _243, _244, _245, _246, _247, TMP269, _248, TMP270, _249, _250, _251, TMP271, usr$x_12, _252, _253, _254, TMP272, usr$y_12, usr$xx_12, _255, _256, _257, _258, _259, TMP273, _260, TMP274, TMP275, _261, usr$recursiveProofLengthInWords, TMP276, _262, _263, TMP277, _264, _265, _266, _267, TMP279, usr$x_13, _268, _269, TMP280, usr$y_13, usr$xx_13, _270, _271, _272, _273, _274, TMP281, _275, TMP282, _276, _277, TMP283, usr$x_14, _278, _279, TMP284, usr$y_14, usr$xx_14, _280, _281, _282, _283, _284, TMP285, _285, TMP286, _286, _287, _288, TMP287;
      {
      _1 <- 4;
      TMP181 <@ CallDataLoad(_1);
      usr$offset <- TMP181;
      _2 <- usr$offset + _1;
      TMP182 <@ CallDataLoad(_2);
      usr$publicInputLengthInWords <- TMP182;
      _3 <- 1;
      usr$isValid <- usr$publicInputLengthInWords = _3;
      _4 <- 253 << 1 - 1;
      _5 <- 36;
      _6 <- usr$offset + _5;
      TMP183 <@ CallDataLoad(_6);
      _7 <- TMP183;
      _8 <- _7 /\ _4;
      _9 <- 1824;
      TMP184 <@ MStore(_9, _8);
      TMP184;
      TMP185 <@ CallDataLoad(_5);
      usr$offset <- TMP185;
      _10 <- usr$offset + _1;
      TMP186 <@ CallDataLoad(_10);
      usr$proofLengthInWords <- TMP186;
      _11 <- 44;
      _12 <- usr$proofLengthInWords = _11;
      usr$isValid <- _12 /\ usr$isValid;
      _13 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
      _14 <- usr$offset + _5;
      TMP187 <@ CallDataLoad(_14);
      _15 <- TMP187;
      usr$x <- _15 % _13;
      _16 <- 68;
      _17 <- usr$offset + _16;
      TMP188 <@ CallDataLoad(_17);
      _18 <- TMP188;
      usr$y <- _18 % _13;
      usr$xx <- mulmod(usr$x, usr$x, _13);
      _19 <- 3;
      _20 <- mulmod(usr$x, usr$xx, _13);
      _21 <- addmod(_20, _19, _13);
      _22 <- mulmod(usr$y, usr$y, _13);
      _23 <- _22 = _21;
      usr$isValid <- _23 /\ usr$isValid;
      _24 <- 1856;
      TMP189 <@ MStore(_24, usr$x);
      TMP189;
      _25 <- 1888;
      TMP190 <@ MStore(_25, usr$y);
      TMP190;
      _26 <- 100;
      _27 <- usr$offset + _26;
      TMP191 <@ CallDataLoad(_27);
      _28 <- TMP191;
      usr$x_1 <- _28 % _13;
      _29 <- 132;
      _30 <- usr$offset + _29;
      TMP192 <@ CallDataLoad(_30);
      _31 <- TMP192;
      usr$y_1 <- _31 % _13;
      usr$xx_1 <- mulmod(usr$x_1, usr$x_1, _13);
      _32 <- mulmod(usr$x_1, usr$xx_1, _13);
      _33 <- addmod(_32, _19, _13);
      _34 <- mulmod(usr$y_1, usr$y_1, _13);
      _35 <- _34 = _33;
      usr$isValid <- _35 /\ usr$isValid;
      _36 <- 1920;
      TMP193 <@ MStore(_36, usr$x_1);
      TMP193;
      _37 <- 1952;
      TMP194 <@ MStore(_37, usr$y_1);
      TMP194;
      _38 <- 164;
      _39 <- usr$offset + _38;
      TMP195 <@ CallDataLoad(_39);
      _40 <- TMP195;
      usr$x_2 <- _40 % _13;
      _41 <- 196;
      _42 <- usr$offset + _41;
      TMP196 <@ CallDataLoad(_42);
      _43 <- TMP196;
      usr$y_2 <- _43 % _13;
      usr$xx_2 <- mulmod(usr$x_2, usr$x_2, _13);
      _44 <- mulmod(usr$x_2, usr$xx_2, _13);
      _45 <- addmod(_44, _19, _13);
      _46 <- mulmod(usr$y_2, usr$y_2, _13);
      _47 <- _46 = _45;
      usr$isValid <- _47 /\ usr$isValid;
      _48 <- 1984;
      TMP197 <@ MStore(_48, usr$x_2);
      TMP197;
      _49 <- 2016;
      TMP198 <@ MStore(_49, usr$y_2);
      TMP198;
      _50 <- 228;
      _51 <- usr$offset + _50;
      TMP199 <@ CallDataLoad(_51);
      _52 <- TMP199;
      usr$x_3 <- _52 % _13;
      _53 <- 260;
      _54 <- usr$offset + _53;
      TMP200 <@ CallDataLoad(_54);
      _55 <- TMP200;
      usr$y_3 <- _55 % _13;
      usr$xx_3 <- mulmod(usr$x_3, usr$x_3, _13);
      _56 <- mulmod(usr$x_3, usr$xx_3, _13);
      _57 <- addmod(_56, _19, _13);
      _58 <- mulmod(usr$y_3, usr$y_3, _13);
      _59 <- _58 = _57;
      usr$isValid <- _59 /\ usr$isValid;
      _60 <- 2048;
      TMP201 <@ MStore(_60, usr$x_3);
      TMP201;
      _61 <- 2080;
      TMP202 <@ MStore(_61, usr$y_3);
      TMP202;
      _62 <- 292;
      _63 <- usr$offset + _62;
      TMP203 <@ CallDataLoad(_63);
      _64 <- TMP203;
      usr$x_4 <- _64 % _13;
      _65 <- 324;
      _66 <- usr$offset + _65;
      TMP204 <@ CallDataLoad(_66);
      _67 <- TMP204;
      usr$y_4 <- _67 % _13;
      usr$xx_4 <- mulmod(usr$x_4, usr$x_4, _13);
      _68 <- mulmod(usr$x_4, usr$xx_4, _13);
      _69 <- addmod(_68, _19, _13);
      _70 <- mulmod(usr$y_4, usr$y_4, _13);
      _71 <- _70 = _69;
      usr$isValid <- _71 /\ usr$isValid;
      _72 <- 2112;
      TMP205 <@ MStore(_72, usr$x_4);
      TMP205;
      _73 <- 2144;
      TMP206 <@ MStore(_73, usr$y_4);
      TMP206;
      _74 <- 356;
      _75 <- usr$offset + _74;
      TMP207 <@ CallDataLoad(_75);
      _76 <- TMP207;
      usr$x_5 <- _76 % _13;
      _77 <- 388;
      _78 <- usr$offset + _77;
      TMP208 <@ CallDataLoad(_78);
      _79 <- TMP208;
      usr$y_5 <- _79 % _13;
      usr$xx_5 <- mulmod(usr$x_5, usr$x_5, _13);
      _80 <- mulmod(usr$x_5, usr$xx_5, _13);
      _81 <- addmod(_80, _19, _13);
      _82 <- mulmod(usr$y_5, usr$y_5, _13);
      _83 <- _82 = _81;
      usr$isValid <- _83 /\ usr$isValid;
      _84 <- 2176;
      TMP209 <@ MStore(_84, usr$x_5);
      TMP209;
      _85 <- 2208;
      TMP210 <@ MStore(_85, usr$y_5);
      TMP210;
      _86 <- 420;
      _87 <- usr$offset + _86;
      TMP211 <@ CallDataLoad(_87);
      _88 <- TMP211;
      usr$x_6 <- _88 % _13;
      _89 <- 452;
      _90 <- usr$offset + _89;
      TMP212 <@ CallDataLoad(_90);
      _91 <- TMP212;
      usr$y_6 <- _91 % _13;
      usr$xx_6 <- mulmod(usr$x_6, usr$x_6, _13);
      _92 <- mulmod(usr$x_6, usr$xx_6, _13);
      _93 <- addmod(_92, _19, _13);
      _94 <- mulmod(usr$y_6, usr$y_6, _13);
      _95 <- _94 = _93;
      usr$isValid <- _95 /\ usr$isValid;
      _96 <- 2240;
      TMP213 <@ MStore(_96, usr$x_6);
      TMP213;
      _97 <- 2272;
      TMP214 <@ MStore(_97, usr$y_6);
      TMP214;
      _98 <- 484;
      _99 <- usr$offset + _98;
      TMP215 <@ CallDataLoad(_99);
      _100 <- TMP215;
      usr$x_7 <- _100 % _13;
      _101 <- 516;
      _102 <- usr$offset + _101;
      TMP216 <@ CallDataLoad(_102);
      _103 <- TMP216;
      usr$y_7 <- _103 % _13;
      usr$xx_7 <- mulmod(usr$x_7, usr$x_7, _13);
      _104 <- mulmod(usr$x_7, usr$xx_7, _13);
      _105 <- addmod(_104, _19, _13);
      _106 <- mulmod(usr$y_7, usr$y_7, _13);
      _107 <- _106 = _105;
      usr$isValid <- _107 /\ usr$isValid;
      _108 <- 2304;
      TMP217 <@ MStore(_108, usr$x_7);
      TMP217;
      _109 <- 2336;
      TMP218 <@ MStore(_109, usr$y_7);
      TMP218;
      _110 <- 548;
      _111 <- usr$offset + _110;
      TMP219 <@ CallDataLoad(_111);
      _112 <- TMP219;
      usr$x_8 <- _112 % _13;
      _113 <- 580;
      _114 <- usr$offset + _113;
      TMP220 <@ CallDataLoad(_114);
      _115 <- TMP220;
      usr$y_8 <- _115 % _13;
      usr$xx_8 <- mulmod(usr$x_8, usr$x_8, _13);
      _116 <- mulmod(usr$x_8, usr$xx_8, _13);
      _117 <- addmod(_116, _19, _13);
      _118 <- mulmod(usr$y_8, usr$y_8, _13);
      _119 <- _118 = _117;
      usr$isValid <- _119 /\ usr$isValid;
      _120 <- 2368;
      TMP221 <@ MStore(_120, usr$x_8);
      TMP221;
      _121 <- 2400;
      TMP222 <@ MStore(_121, usr$y_8);
      TMP222;
      _122 <- 612;
      _123 <- usr$offset + _122;
      TMP223 <@ CallDataLoad(_123);
      _124 <- TMP223;
      usr$x_9 <- _124 % _13;
      _125 <- 644;
      _126 <- usr$offset + _125;
      TMP224 <@ CallDataLoad(_126);
      _127 <- TMP224;
      usr$y_9 <- _127 % _13;
      usr$xx_9 <- mulmod(usr$x_9, usr$x_9, _13);
      _128 <- mulmod(usr$x_9, usr$xx_9, _13);
      _129 <- addmod(_128, _19, _13);
      _130 <- mulmod(usr$y_9, usr$y_9, _13);
      _131 <- _130 = _129;
      usr$isValid <- _131 /\ usr$isValid;
      _132 <- 2432;
      TMP225 <@ MStore(_132, usr$x_9);
      TMP225;
      _133 <- 2464;
      TMP226 <@ MStore(_133, usr$y_9);
      TMP226;
      _134 <- 676;
      _135 <- usr$offset + _134;
      TMP227 <@ CallDataLoad(_135);
      _136 <- TMP227;
      usr$x_10 <- _136 % _13;
      _137 <- 708;
      _138 <- usr$offset + _137;
      TMP228 <@ CallDataLoad(_138);
      _139 <- TMP228;
      usr$y_10 <- _139 % _13;
      usr$xx_10 <- mulmod(usr$x_10, usr$x_10, _13);
      _140 <- mulmod(usr$x_10, usr$xx_10, _13);
      _141 <- addmod(_140, _19, _13);
      _142 <- mulmod(usr$y_10, usr$y_10, _13);
      _143 <- _142 = _141;
      usr$isValid <- _143 /\ usr$isValid;
      _144 <- 2496;
      TMP229 <@ MStore(_144, usr$x_10);
      TMP229;
      _145 <- 2528;
      TMP230 <@ MStore(_145, usr$y_10);
      TMP230;
      _146 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _147 <- 740;
      _148 <- usr$offset + _147;
      TMP231 <@ CallDataLoad(_148);
      _149 <- TMP231;
      _150 <- _149 % _146;
      _151 <- 2560;
      TMP232 <@ MStore(_151, _150);
      TMP232;
      _152 <- 772;
      _153 <- usr$offset + _152;
      TMP233 <@ CallDataLoad(_153);
      _154 <- TMP233;
      _155 <- _154 % _146;
      _156 <- 2592;
      TMP234 <@ MStore(_156, _155);
      TMP234;
      _157 <- 804;
      _158 <- usr$offset + _157;
      TMP235 <@ CallDataLoad(_158);
      _159 <- TMP235;
      _160 <- _159 % _146;
      _161 <- 2624;
      TMP236 <@ MStore(_161, _160);
      TMP236;
      _162 <- 836;
      _163 <- usr$offset + _162;
      TMP237 <@ CallDataLoad(_163);
      _164 <- TMP237;
      _165 <- _164 % _146;
      _166 <- 2656;
      TMP238 <@ MStore(_166, _165);
      TMP238;
      _167 <- 868;
      _168 <- usr$offset + _167;
      TMP239 <@ CallDataLoad(_168);
      _169 <- TMP239;
      _170 <- _169 % _146;
      _171 <- 2688;
      TMP240 <@ MStore(_171, _170);
      TMP240;
      _172 <- 900;
      _173 <- usr$offset + _172;
      TMP241 <@ CallDataLoad(_173);
      _174 <- TMP241;
      _175 <- _174 % _146;
      _176 <- 2720;
      TMP242 <@ MStore(_176, _175);
      TMP242;
      _177 <- 932;
      _178 <- usr$offset + _177;
      TMP243 <@ CallDataLoad(_178);
      _179 <- TMP243;
      _180 <- _179 % _146;
      _181 <- 2752;
      TMP244 <@ MStore(_181, _180);
      TMP244;
      _182 <- 964;
      _183 <- usr$offset + _182;
      TMP245 <@ CallDataLoad(_183);
      _184 <- TMP245;
      _185 <- _184 % _146;
      _186 <- 2784;
      TMP246 <@ MStore(_186, _185);
      TMP246;
      _187 <- 996;
      _188 <- usr$offset + _187;
      TMP247 <@ CallDataLoad(_188);
      _189 <- TMP247;
      _190 <- _189 % _146;
      _191 <- 2816;
      TMP248 <@ MStore(_191, _190);
      TMP248;
      _192 <- 1028;
      _193 <- usr$offset + _192;
      TMP249 <@ CallDataLoad(_193);
      _194 <- TMP249;
      _195 <- _194 % _146;
      _196 <- 2848;
      TMP250 <@ MStore(_196, _195);
      TMP250;
      _197 <- 1060;
      _198 <- usr$offset + _197;
      TMP251 <@ CallDataLoad(_198);
      _199 <- TMP251;
      _200 <- _199 % _146;
      _201 <- 2880;
      TMP252 <@ MStore(_201, _200);
      TMP252;
      _202 <- 1092;
      _203 <- usr$offset + _202;
      TMP253 <@ CallDataLoad(_203);
      _204 <- TMP253;
      _205 <- _204 % _146;
      _206 <- 2912;
      TMP254 <@ MStore(_206, _205);
      TMP254;
      _207 <- 1124;
      _208 <- usr$offset + _207;
      TMP255 <@ CallDataLoad(_208);
      _209 <- TMP255;
      _210 <- _209 % _146;
      _211 <- 2944;
      TMP256 <@ MStore(_211, _210);
      TMP256;
      _212 <- 1156;
      _213 <- usr$offset + _212;
      TMP257 <@ CallDataLoad(_213);
      _214 <- TMP257;
      _215 <- _214 % _146;
      _216 <- 2976;
      TMP258 <@ MStore(_216, _215);
      TMP258;
      _217 <- 1188;
      _218 <- usr$offset + _217;
      TMP259 <@ CallDataLoad(_218);
      _219 <- TMP259;
      _220 <- _219 % _146;
      _221 <- 3008;
      TMP260 <@ MStore(_221, _220);
      TMP260;
      _222 <- 1220;
      _223 <- usr$offset + _222;
      TMP261 <@ CallDataLoad(_223);
      _224 <- TMP261;
      _225 <- _224 % _146;
      _226 <- 3040;
      TMP262 <@ MStore(_226, _225);
      TMP262;
      _227 <- 1252;
      _228 <- usr$offset + _227;
      TMP263 <@ CallDataLoad(_228);
      _229 <- TMP263;
      _230 <- _229 % _146;
      _231 <- 3072;
      TMP264 <@ MStore(_231, _230);
      TMP264;
      _232 <- 1284;
      _233 <- usr$offset + _232;
      TMP265 <@ CallDataLoad(_233);
      _234 <- TMP265;
      _235 <- _234 % _146;
      _236 <- 3104;
      TMP266 <@ MStore(_236, _235);
      TMP266;
      _237 <- 1316;
      _238 <- usr$offset + _237;
      TMP267 <@ CallDataLoad(_238);
      _239 <- TMP267;
      usr$x_11 <- _239 % _13;
      _240 <- 1348;
      _241 <- usr$offset + _240;
      TMP268 <@ CallDataLoad(_241);
      _242 <- TMP268;
      usr$y_11 <- _242 % _13;
      usr$xx_11 <- mulmod(usr$x_11, usr$x_11, _13);
      _243 <- mulmod(usr$x_11, usr$xx_11, _13);
      _244 <- addmod(_243, _19, _13);
      _245 <- mulmod(usr$y_11, usr$y_11, _13);
      _246 <- _245 = _244;
      usr$isValid <- _246 /\ usr$isValid;
      _247 <- 3136;
      TMP269 <@ MStore(_247, usr$x_11);
      TMP269;
      _248 <- 3168;
      TMP270 <@ MStore(_248, usr$y_11);
      TMP270;
      _249 <- 1380;
      _250 <- usr$offset + _249;
      TMP271 <@ CallDataLoad(_250);
      _251 <- TMP271;
      usr$x_12 <- _251 % _13;
      _252 <- 1412;
      _253 <- usr$offset + _252;
      TMP272 <@ CallDataLoad(_253);
      _254 <- TMP272;
      usr$y_12 <- _254 % _13;
      usr$xx_12 <- mulmod(usr$x_12, usr$x_12, _13);
      _255 <- mulmod(usr$x_12, usr$xx_12, _13);
      _256 <- addmod(_255, _19, _13);
      _257 <- mulmod(usr$y_12, usr$y_12, _13);
      _258 <- _257 = _256;
      usr$isValid <- _258 /\ usr$isValid;
      _259 <- 3200;
      TMP273 <@ MStore(_259, usr$x_12);
      TMP273;
      _260 <- 3232;
      TMP274 <@ MStore(_260, usr$y_12);
      TMP274;
      TMP275 <@ CallDataLoad(_16);
      usr$offset <- TMP275;
      _261 <- usr$offset + _1;
      TMP276 <@ CallDataLoad(_261);
      usr$recursiveProofLengthInWords <- TMP276;
      _262 <- 1792;
      TMP277 <@ MLoad(_262);
      _263 <- TMP277;
      TMP278 <- _263;
      if (TMP278 = 0)
        {
        _264 <- iszero(usr$recursiveProofLengthInWords);
        usr$isValid <- _264 /\ usr$isValid;
        
        }
      
      else {
        _265 <- usr$recursiveProofLengthInWords = _1;
        usr$isValid <- _265 /\ usr$isValid;
        _266 <- usr$offset + _5;
        TMP279 <@ CallDataLoad(_266);
        _267 <- TMP279;
        usr$x_13 <- _267 % _13;
        _268 <- usr$offset + _16;
        TMP280 <@ CallDataLoad(_268);
        _269 <- TMP280;
        usr$y_13 <- _269 % _13;
        usr$xx_13 <- mulmod(usr$x_13, usr$x_13, _13);
        _270 <- mulmod(usr$x_13, usr$xx_13, _13);
        _271 <- addmod(_270, _19, _13);
        _272 <- mulmod(usr$y_13, usr$y_13, _13);
        _273 <- _272 = _271;
        usr$isValid <- _273 /\ usr$isValid;
        _274 <- 3264;
        TMP281 <@ MStore(_274, usr$x_13);
        TMP281;
        _275 <- 3296;
        TMP282 <@ MStore(_275, usr$y_13);
        TMP282;
        _276 <- usr$offset + _26;
        TMP283 <@ CallDataLoad(_276);
        _277 <- TMP283;
        usr$x_14 <- _277 % _13;
        _278 <- usr$offset + _29;
        TMP284 <@ CallDataLoad(_278);
        _279 <- TMP284;
        usr$y_14 <- _279 % _13;
        usr$xx_14 <- mulmod(usr$x_14, usr$x_14, _13);
        _280 <- mulmod(usr$x_14, usr$xx_14, _13);
        _281 <- addmod(_280, _19, _13);
        _282 <- mulmod(usr$y_14, usr$y_14, _13);
        _283 <- _282 = _281;
        usr$isValid <- _283 /\ usr$isValid;
        _284 <- 3328;
        TMP285 <@ MStore(_284, usr$x_14);
        TMP285;
        _285 <- 3360;
        TMP286 <@ MStore(_285, usr$y_14);
        TMP286;
        
        }
      ;
      _286 <- iszero(usr$isValid);
      if (_286)
        {
        _287 <- "loadProof: Proof is invalid";
        _288 <- 27;
        TMP287 <@ usr$revertWithMessage(_288, _287);
        TMP287;
        
        }
      ;
      
      }
    }
  
  proc abi_encode_bytes32_to_bytes32(value : uint256, pos : uint256): unit = {
    var _1, TMP44;
      {
      _1 <- cleanup_bytes32(value);
      TMP44 <@ MStore(pos, _1);
      TMP44;
      
      }
    }
  
  proc usr$prepareQueries(): unit = {
    var _1, usr$zInDomainSize, TMP510, usr$currentZ, _2, _3, TMP511, _4, TMP512, _5, _6, TMP513, _7, TMP514, _8, TMP515, _9, _10, TMP516, _11, TMP517, _12, usr$stateOpening0AtZ, TMP518, _13, usr$stateOpening1AtZ, TMP519, _14, usr$stateOpening2AtZ, TMP520, _15, usr$stateOpening3AtZ, TMP521, _16, TMP522, TMP523, TMP524, TMP525, _17, _18, TMP526, _19, TMP527, _20, _21, TMP528, _22, TMP529, _23, usr$eta, TMP530, usr$currentEta, _24, TMP531, _25, TMP532, _26, TMP533;
      {
      _1 <- 4192;
      TMP510 <@ MLoad(_1);
      usr$zInDomainSize <- TMP510;
      usr$currentZ <- usr$zInDomainSize;
      _2 <- 2304;
      TMP511 <@ MLoad(_2);
      _3 <- TMP511;
      _4 <- 4288;
      TMP512 <@ MStore(_4, _3);
      TMP512;
      _5 <- 2336;
      TMP513 <@ MLoad(_5);
      _6 <- TMP513;
      _7 <- 4320;
      TMP514 <@ MStore(_7, _6);
      TMP514;
      _8 <- 2368;
      TMP515 <@ usr$pointMulAndAddIntoDest(_8, usr$zInDomainSize, _4);
      TMP515;
      _9 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      usr$currentZ <- mulmod(usr$zInDomainSize, usr$zInDomainSize, _9);
      _10 <- 2432;
      TMP516 <@ usr$pointMulAndAddIntoDest(_10, usr$currentZ, _4);
      TMP516;
      usr$currentZ <- mulmod(usr$currentZ, usr$zInDomainSize, _9);
      _11 <- 2496;
      TMP517 <@ usr$pointMulAndAddIntoDest(_11, usr$currentZ, _4);
      TMP517;
      _12 <- 2560;
      TMP518 <@ MLoad(_12);
      usr$stateOpening0AtZ <- TMP518;
      _13 <- 2592;
      TMP519 <@ MLoad(_13);
      usr$stateOpening1AtZ <- TMP519;
      _14 <- 2624;
      TMP520 <@ MLoad(_14);
      usr$stateOpening2AtZ <- TMP520;
      _15 <- 2656;
      TMP521 <@ MLoad(_15);
      usr$stateOpening3AtZ <- TMP521;
      _16 <- 4352;
      TMP522 <@ usr$mainGateLinearisationContributionWithV(_16, usr$stateOpening0AtZ, usr$stateOpening1AtZ, usr$stateOpening2AtZ, usr$stateOpening3AtZ);
      TMP522;
      TMP523 <@ usr$addAssignRescueCustomGateLinearisationContributionWithV(_16, usr$stateOpening0AtZ, usr$stateOpening1AtZ, usr$stateOpening2AtZ, usr$stateOpening3AtZ);
      TMP523;
      TMP524 <@ usr$addAssignPermutationLinearisationContributionWithV(_16, usr$stateOpening0AtZ, usr$stateOpening1AtZ, usr$stateOpening2AtZ, usr$stateOpening3AtZ);
      TMP524;
      TMP525 <@ usr$addAssignLookupLinearisationContributionWithV(_16, usr$stateOpening0AtZ, usr$stateOpening1AtZ, usr$stateOpening2AtZ);
      TMP525;
      _17 <- 1472;
      TMP526 <@ MLoad(_17);
      _18 <- TMP526;
      _19 <- 4416;
      TMP527 <@ MStore(_19, _18);
      TMP527;
      _20 <- 1504;
      TMP528 <@ MLoad(_20);
      _21 <- TMP528;
      _22 <- 4448;
      TMP529 <@ MStore(_22, _21);
      TMP529;
      _23 <- 3840;
      TMP530 <@ MLoad(_23);
      usr$eta <- TMP530;
      usr$currentEta <- usr$eta;
      _24 <- 1536;
      TMP531 <@ usr$pointMulAndAddIntoDest(_24, usr$eta, _19);
      TMP531;
      usr$currentEta <- mulmod(usr$eta, usr$eta, _9);
      _25 <- 1600;
      TMP532 <@ usr$pointMulAndAddIntoDest(_25, usr$currentEta, _19);
      TMP532;
      usr$currentEta <- mulmod(usr$currentEta, usr$eta, _9);
      _26 <- 1664;
      TMP533 <@ usr$pointMulAndAddIntoDest(_26, usr$currentEta, _19);
      TMP533;
      
      }
    }
  
  proc shift_right_unsigned(value : uint256): uint256 = {
    var newValue, _1;
      {
      _1 <- 224;
      newValue <- _1 >> value;
      return newValue;
      
      }
    }
  
  proc fun_loadVerificationKey(): unit = {
    var _1, _2, TMP56, _3, _4, TMP57, _5, _6, TMP58, _7, _8, TMP59, _9, _10, TMP60, _11, _12, TMP61, _13, _14, TMP62, _15, _16, TMP63, _17, _18, TMP64, _19, _20, TMP65, _21, _22, TMP66, _23, _24, TMP67, _25, _26, TMP68, _27, _28, TMP69, _29, _30, TMP70, _31, _32, TMP71, _33, _34, TMP72, _35, _36, TMP73, _37, _38, TMP74, _39, _40, TMP75, _41, _42, TMP76, _43, _44, TMP77, _45, _46, TMP78, _47, _48, TMP79, _49, _50, TMP80, _51, _52, TMP81, _53, _54, TMP82, _55, _56, TMP83, _57, _58, TMP84, _59, _60, TMP85, _61, _62, TMP86, _63, _64, TMP87, _65, _66, TMP88, _67, _68, TMP89, _69, _70, TMP90, _71, _72, TMP91, _73, _74, TMP92, _75, _76, TMP93, _77, _78, TMP94, _79, _80, TMP95, _81, _82, TMP96;
      {
      _1 <- 8752182643819278825281358491109311747488397345835400146720638359015287854690;
      _2 <- 512;
      TMP56 <@ MStore(_2, _1);
      TMP56;
      _3 <- 11702890106774794311109464320829961639285524182517416836480964755620593036625;
      _4 <- 544;
      TMP57 <@ MStore(_4, _3);
      TMP57;
      _5 <- 20333726085237242816528533108173405517277666887513325731527458638169740323846;
      _6 <- 576;
      TMP58 <@ MStore(_6, _5);
      TMP58;
      _7 <- 20895759739260899082484353863151962651671811489085862903974918191239970565727;
      _8 <- 608;
      TMP59 <@ MStore(_8, _7);
      TMP59;
      _9 <- 1568732599965362807326380099663611053862348508639087822144187543479274466412;
      _10 <- 640;
      TMP60 <@ MStore(_10, _9);
      TMP60;
      _11 <- 5821054758250780059685638301776364871013117602597489359484409980131967326794;
      _12 <- 672;
      TMP61 <@ MStore(_12, _11);
      TMP61;
      _13 <- 1869564366554527726271945732583360837778279311090061338642468249261166609475;
      _14 <- 704;
      TMP62 <@ MStore(_14, _13);
      TMP62;
      _15 <- 6787073056745945161826226704190290609825180409911049644428579916838155209697;
      _16 <- 736;
      TMP63 <@ MStore(_16, _15);
      TMP63;
      _17 <- 457576930265342335264945522969406804501107665328727087867171094316559181535;
      _18 <- 768;
      TMP64 <@ MStore(_18, _17);
      TMP64;
      _19 <- 15424863073888926344027107060444259361026863904290125685775015743583967752523;
      _20 <- 800;
      TMP65 <@ MStore(_20, _19);
      TMP65;
      _21 <- 17470132079837949645292768946901897910488674334073656384858846314172720305794;
      _22 <- 832;
      TMP66 <@ MStore(_22, _21);
      TMP66;
      _23 <- 545412623592733862227844066395948813122937527333953380716629283051527996076;
      _24 <- 864;
      TMP67 <@ MStore(_24, _23);
      TMP67;
      _25 <- 3542620684081214281078362979824071457719243923292217179618867142734017714197;
      _26 <- 896;
      TMP68 <@ MStore(_26, _25);
      TMP68;
      _27 <- 10380438707000372753007289103897630883671902212004026295360039945231108187502;
      _28 <- 928;
      TMP69 <@ MStore(_28, _27);
      TMP69;
      _29 <- 13086775255118926036233880981068687796723800497694631087151014741591951564618;
      _30 <- 960;
      TMP70 <@ MStore(_30, _29);
      TMP70;
      _31 <- 97194583370920108185062801930585216368005987855712538133473341181290744675;
      _32 <- 992;
      TMP71 <@ MStore(_32, _31);
      TMP71;
      _33 <- 11090534100914016361232447120294745393211436081860550365760620284449885924457;
      _34 <- 1024;
      TMP72 <@ MStore(_34, _33);
      TMP72;
      _35 <- 6190121082107679677011313308624936965782748053078710395209485205617091614781;
      _36 <- 1056;
      TMP73 <@ MStore(_36, _35);
      TMP73;
      _37 <- 15086136319636422536776088427553286399949509263897119922379735045147898875009;
      _38 <- 1088;
      TMP74 <@ MStore(_38, _37);
      TMP74;
      _39 <- 14330561162787072568797012175184761164763459595199124517037991495673925464785;
      _40 <- 1120;
      TMP75 <@ MStore(_40, _39);
      TMP75;
      _41 <- 21323538885080684424185174689480993185750201390966223018512354418490677522148;
      _42 <- 1152;
      TMP76 <@ MStore(_42, _41);
      TMP76;
      _43 <- 13825385863192118646834397710139923872086647553258488355179808994788744210563;
      _44 <- 1184;
      TMP77 <@ MStore(_44, _43);
      TMP77;
      _45 <- 8390759602848414205412884900126185284679301543388803089358900543850868129488;
      _46 <- 1216;
      TMP78 <@ MStore(_46, _45);
      TMP78;
      _47 <- 7069161667387011886642940009688789554068768218554020114127791736575843662652;
      _48 <- 1248;
      TMP79 <@ MStore(_48, _47);
      TMP79;
      _49 <- 21779692208264067614279093821878517213862501879831804234566704419708093761485;
      _50 <- 1280;
      TMP80 <@ MStore(_50, _49);
      TMP80;
      _51 <- 14513193766097634962386283396255157053671281137962954471134782133605379519908;
      _52 <- 1312;
      TMP81 <@ MStore(_52, _51);
      TMP81;
      _53 <- 4751267043421347170875860608378639586591867931662910797110300384786346064625;
      _54 <- 1344;
      TMP82 <@ MStore(_54, _53);
      TMP82;
      _55 <- 11385717438670984215358012358002661303410243223751533068904005282628107986385;
      _56 <- 1376;
      TMP83 <@ MStore(_56, _55);
      TMP83;
      _57 <- 20045313662746578028950791395157660351198208045597010788369662325700141348443;
      _58 <- 1472;
      TMP84 <@ MStore(_58, _57);
      TMP84;
      _59 <- 2200761695078532224145807378118591946349840073460005094399078719163643466856;
      _60 <- 1504;
      TMP85 <@ MStore(_60, _59);
      TMP85;
      _61 <- 13866646217607640441607041956684111087071997201218815349460750486791109380780;
      _62 <- 1536;
      TMP86 <@ MStore(_62, _61);
      TMP86;
      _63 <- 13178446611795019678701878053235714968797421377761816259103804833273256298333;
      _64 <- 1568;
      TMP87 <@ MStore(_64, _63);
      TMP87;
      _65 <- 5057503605752869531452842486824745179648819794307492731589448195268672785801;
      _66 <- 1600;
      TMP88 <@ MStore(_66, _65);
      TMP88;
      _67 <- 8597434312520299647191152876265164941580478223412397470356037586993894367875;
      _68 <- 1632;
      TMP89 <@ MStore(_68, _67);
      TMP89;
      _69 <- 1342318055425277544055386589364579054544440640110901993487861472578322387903;
      _70 <- 1664;
      TMP90 <@ MStore(_70, _69);
      TMP90;
      _71 <- 4438354282468267034382897187461199764068502038746983055473062465446039509158;
      _72 <- 1696;
      TMP91 <@ MStore(_72, _71);
      TMP91;
      _73 <- 21714794642552531775933093644480516421064284615960245486122726724547638127878;
      _74 <- 1408;
      TMP92 <@ MStore(_74, _73);
      TMP92;
      _75 <- 20374981665942106195451736226451722737514281476778224282304648903722926579601;
      _76 <- 1440;
      TMP93 <@ MStore(_76, _75);
      TMP93;
      _77 <- 196778531949039689886328474582670216324308721975620885373710029662715787742;
      _78 <- 1728;
      TMP94 <@ MStore(_78, _77);
      TMP94;
      _79 <- 11005776646725047106517461026899305486268481542412200771754169232553006481646;
      _80 <- 1760;
      TMP95 <@ MStore(_80, _79);
      TMP95;
      _81 <- 0;
      _82 <- 1792;
      TMP96 <@ MStore(_82, _81);
      TMP96;
      
      }
    }
  
  proc revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc usr$pointAddIntoDest(usr$p1 : uint256, usr$p2 : uint256, usr$dest : uint256): unit = {
    var _1, TMP119, _2, TMP120, _3, _4, _5, TMP121, TMP122, _6, TMP123, _7, TMP124, _8, _9, TMP125, _10, TMP126, _11, _12, _13, TMP127, _14, TMP128, _15, _16, _17, TMP129;
      {
      TMP119 <@ MLoad(usr$p1);
      _1 <- TMP119;
      _2 <- 0;
      TMP120 <@ MStore(_2, _1);
      TMP120;
      _3 <- 32;
      _4 <- usr$p1 + _3;
      TMP121 <@ MLoad(_4);
      _5 <- TMP121;
      TMP122 <@ MStore(_3, _5);
      TMP122;
      TMP123 <@ MLoad(usr$p2);
      _6 <- TMP123;
      _7 <- 64;
      TMP124 <@ MStore(_7, _6);
      TMP124;
      _8 <- usr$p2 + _3;
      TMP125 <@ MLoad(_8);
      _9 <- TMP125;
      _10 <- 96;
      TMP126 <@ MStore(_10, _9);
      TMP126;
      _11 <- 128;
      _12 <- 6;
      TMP127 <@ Gas();
      _13 <- TMP127;
      TMP128 <@ StaticCall(_13, _12, _2, _11, usr$dest, _7);
      _14 <- TMP128;
      _15 <- iszero(_14);
      if (_15)
        {
        _16 <- "pointAddIntoDest: ecAdd failed";
        _17 <- 30;
        TMP129 <@ usr$revertWithMessage(_17, _16);
        TMP129;
        
        }
      ;
      
      }
    }
  
  proc usr$addAssignPermutationLinearisationContributionWithV(usr$dest : uint256, usr$stateOpening0AtZ : uint256, usr$stateOpening1AtZ : uint256, usr$stateOpening2AtZ : uint256, usr$stateOpening3AtZ : uint256): unit = {
    var usr$factor, TMP469, _1, TMP470, _2, _3, TMP471, usr$gamma, TMP472, _4, usr$intermediateValue, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, usr$l0AtZ, TMP473, _15, _16, TMP474, _17, _18, TMP475, _19, TMP476, _20, TMP477, _21, TMP478, _22, _23, TMP479, usr$beta, TMP480, usr$gamma_1, TMP481, _24, _25, TMP482, _26, _27, usr$intermediateValue_1, _28, _29, TMP483, _30, _31, _32, _33, TMP484, _34, _35, _36, TMP485, _37, _38, TMP486, TMP487;
      {
      TMP469 <@ MLoad(3680);
      usr$factor <- TMP469;
      TMP470 <@ MLoad(3552);
      _1 <- TMP470;
      _2 <- 4064;
      TMP471 <@ MLoad(_2);
      _3 <- TMP471;
      TMP472 <@ MLoad(3584);
      usr$gamma <- TMP472;
      _4 <- addmod(mulmod(_3, _1, 21888242871839275222246405745257275088548364400416034343698204186575808495617), usr$gamma, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$intermediateValue <- addmod(_4, usr$stateOpening0AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$intermediateValue, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _5 <- 5;
      _6 <- mulmod(mulmod(_3, _1, 21888242871839275222246405745257275088548364400416034343698204186575808495617), _5, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _7 <- addmod(_6, usr$gamma, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$intermediateValue <- addmod(_7, usr$stateOpening1AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$intermediateValue, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _8 <- 7;
      _9 <- mulmod(mulmod(_3, _1, 21888242871839275222246405745257275088548364400416034343698204186575808495617), _8, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _10 <- addmod(_9, usr$gamma, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$intermediateValue <- addmod(_10, usr$stateOpening2AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$intermediateValue, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _11 <- 10;
      _12 <- mulmod(mulmod(_3, _1, 21888242871839275222246405745257275088548364400416034343698204186575808495617), _11, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _13 <- addmod(_12, usr$gamma, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$intermediateValue <- addmod(_13, usr$stateOpening3AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$intermediateValue, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _14 <- 4128;
      TMP473 <@ MLoad(_14);
      usr$l0AtZ <- TMP473;
      _15 <- 3712;
      TMP474 <@ MLoad(_15);
      _16 <- TMP474;
      _17 <- mulmod(usr$l0AtZ, _16, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- addmod(usr$factor, _17, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      TMP475 <@ MLoad(4000);
      _18 <- TMP475;
      usr$factor <- mulmod(usr$factor, _18, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _19 <- 4928;
      TMP476 <@ MStore(_19, usr$factor);
      TMP476;
      TMP477 <@ MLoad(3552);
      _20 <- TMP477;
      TMP478 <@ MLoad(3680);
      _21 <- TMP478;
      usr$factor <- mulmod(_21, _20, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _22 <- 2848;
      TMP479 <@ MLoad(_22);
      _23 <- TMP479;
      usr$factor <- mulmod(usr$factor, _23, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      TMP480 <@ MLoad(3552);
      usr$beta <- TMP480;
      TMP481 <@ MLoad(3584);
      usr$gamma_1 <- TMP481;
      _24 <- 2752;
      TMP482 <@ MLoad(_24);
      _25 <- TMP482;
      _26 <- mulmod(_25, usr$beta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _27 <- addmod(_26, usr$gamma_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$intermediateValue_1 <- addmod(_27, usr$stateOpening0AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$intermediateValue_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _28 <- 2784;
      TMP483 <@ MLoad(_28);
      _29 <- TMP483;
      _30 <- mulmod(_29, usr$beta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _31 <- addmod(_30, usr$gamma_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$intermediateValue_1 <- addmod(_31, usr$stateOpening1AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$intermediateValue_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _32 <- 2816;
      TMP484 <@ MLoad(_32);
      _33 <- TMP484;
      _34 <- mulmod(_33, usr$beta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _35 <- addmod(_34, usr$gamma_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$intermediateValue_1 <- addmod(_35, usr$stateOpening2AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$intermediateValue_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      TMP485 <@ MLoad(4000);
      _36 <- TMP485;
      usr$factor <- mulmod(usr$factor, _36, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _37 <- 4224;
      _38 <- 1344;
      TMP486 <@ usr$pointMulIntoDest(_38, usr$factor, _37);
      TMP486;
      TMP487 <@ usr$pointSubAssign(usr$dest, _37);
      TMP487;
      
      }
    }
  
  proc usr$verifyQuotientEvaluation(): unit = {
    var _1, usr$alpha, TMP398, _2, usr$currentAlpha, _3, TMP399, _4, TMP400, _5, TMP401, _6, TMP402, _7, TMP403, _8, TMP404, _9, TMP405, _10, usr$stateZ, TMP406, _11, _12, TMP407, _13, TMP408, _14, _15, _16, _17, TMP409, _18, TMP410, _19, _20, TMP411, _21, TMP412, usr$stateT, _22, _23, TMP413, usr$result, _24, TMP414, _25, TMP415, _26, _27, TMP416, _28, _29, _30, TMP417, usr$vanishing, _31, _32, TMP418, usr$lhs, _33, _34, _35, _36, TMP419;
      {
      _1 <- 3520;
      TMP398 <@ MLoad(_1);
      usr$alpha <- TMP398;
      _2 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      usr$currentAlpha <- mulmod(usr$alpha, usr$alpha, _2);
      _3 <- 3616;
      TMP399 <@ MStore(_3, usr$currentAlpha);
      TMP399;
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _4 <- 3648;
      TMP400 <@ MStore(_4, usr$currentAlpha);
      TMP400;
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _5 <- 3680;
      TMP401 <@ MStore(_5, usr$currentAlpha);
      TMP401;
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _6 <- 3712;
      TMP402 <@ MStore(_6, usr$currentAlpha);
      TMP402;
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _7 <- 3744;
      TMP403 <@ MStore(_7, usr$currentAlpha);
      TMP403;
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _8 <- 3776;
      TMP404 <@ MStore(_8, usr$currentAlpha);
      TMP404;
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _9 <- 3808;
      TMP405 <@ MStore(_9, usr$currentAlpha);
      TMP405;
      _10 <- 4064;
      TMP406 <@ MLoad(_10);
      usr$stateZ <- TMP406;
      _11 <- 0;
      TMP407 <@ usr$evaluateLagrangePolyOutOfDomain(_11, usr$stateZ);
      _12 <- TMP407;
      _13 <- 4128;
      TMP408 <@ MStore(_13, _12);
      TMP408;
      _14 <- 1;
      _15 <- 67108864;
      _16 <- _15 - _14;
      TMP409 <@ usr$evaluateLagrangePolyOutOfDomain(_16, usr$stateZ);
      _17 <- TMP409;
      _18 <- 4160;
      TMP410 <@ MStore(_18, _17);
      TMP410;
      _19 <- 1824;
      TMP411 <@ MLoad(_19);
      _20 <- TMP411;
      TMP412 <@ MLoad(_13);
      _21 <- TMP412;
      usr$stateT <- mulmod(_21, _20, _2);
      _22 <- 2720;
      TMP413 <@ MLoad(_22);
      _23 <- TMP413;
      usr$result <- mulmod(usr$stateT, _23, _2);
      TMP414 <@ usr$permutationQuotientContribution();
      _24 <- TMP414;
      usr$result <- addmod(usr$result, _24, _2);
      TMP415 <@ usr$lookupQuotientContribution();
      _25 <- TMP415;
      usr$result <- addmod(usr$result, _25, _2);
      _26 <- 3104;
      TMP416 <@ MLoad(_26);
      _27 <- TMP416;
      usr$result <- addmod(_27, usr$result, _2);
      _28 <- _2 - _14;
      _29 <- 4192;
      TMP417 <@ MLoad(_29);
      _30 <- TMP417;
      usr$vanishing <- addmod(_30, _28, _2);
      _31 <- 3072;
      TMP418 <@ MLoad(_31);
      _32 <- TMP418;
      usr$lhs <- mulmod(_32, usr$vanishing, _2);
      _33 <- usr$lhs = usr$result;
      _34 <- iszero(_33);
      if (_34)
        {
        _35 <- "invalid quotient evaluation";
        _36 <- 27;
        TMP419 <@ usr$revertWithMessage(_36, _35);
        TMP419;
        
        }
      ;
      
      }
    }
  
  
  }
(* End Verifier_1261 *)
