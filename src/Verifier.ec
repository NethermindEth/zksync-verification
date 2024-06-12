(* Begin Verifier_1261 *)
op cleanup_bytes32(value : uint256): uint256 = value.

op zero_value_for_split_bool: uint256 = 0.

op zero_value_for_split_bytes32: uint256 = 0.

module Verifier_1261 = {
  proc usr$pointNegate(usr$point : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, _2, usr$pY, tmp88, _3, tmp90, _4, _5, tmp91, _6, _7;
      {
      _1 <- 32;
      _2 <- usr$point + _1;
      tmp88 <@ MLoad(_2, param_state_memory);
      usr$pY <- tmp88;
      tmp89 <- usr$pY;
      if (tmp89 = 0)
        {
        tmp90 <@ MLoad(usr$point, param_state_memory);
        _3 <- tmp90;
        if (_3)
          {
          _4 <- "pointNegate: invalid point";
          _5 <- 26;
          tmp91,param_state_memory <@ usr$revertWithMessage(_5, _4, param_state_memory);
          
          }
        ;
        
        }
      
      else {
        _6 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
        _7 <- _6 - usr$pY;
        param_state_memory <@ MStore(_2, _7, param_state_memory);
        
        }
      ;
      return param_state_memory;
      
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
  
  proc abi_encode_bool(headStart : uint256, value0 : uint256, param_state_memory : mem): (uint256 * mem) = {
    var tail, param_state_memory, _1, _2, _3, tmp32;
      {
      _1 <- 32;
      tail <- headStart + _1;
      _2 <- 0;
      _3 <- headStart + _2;
      tmp32,param_state_memory <@ abi_encode_bool_to_bool(value0, _3, param_state_memory);
      return (tail, param_state_memory);
      
      }
    }
  
  proc usr$evaluateLagrangePolyOutOfDomain(usr$polyNum : uint256, usr$at : uint256, param_state_memory : mem): (uint256 * mem) = {
    var usr$res, param_state_memory, usr$omegaPower, _1, tmp266, _2, _3, _4, _5, _6, tmp267, _7, _8, _9, tmp268, _10, usr$denominator, _11, _12, tmp269;
      {
      usr$omegaPower <- 1;
      if (usr$polyNum)
        {
        _1 <- 13446667982376394161563610564587413125564757801019538732601045199901075958935;
        tmp266,param_state_memory <@ usr$modexp(_1, usr$polyNum, param_state_memory);
        usr$omegaPower <- tmp266;
        
        }
      ;
      _2 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _3 <- 1;
      _4 <- _2 - _3;
      _5 <- 67108864;
      tmp267,param_state_memory <@ usr$modexp(usr$at, _5, param_state_memory);
      _6 <- tmp267;
      usr$res <- addmod(_6, _4, _2);
      _7 <- iszero(usr$res);
      if (_7)
        {
        _8 <- "invalid vanishing polynomial";
        _9 <- 28;
        tmp268,param_state_memory <@ usr$revertWithMessage(_9, _8, param_state_memory);
        
        }
      ;
      usr$res <- mulmod(usr$res, usr$omegaPower, _2);
      _10 <- _2 - usr$omegaPower;
      usr$denominator <- addmod(usr$at, _10, _2);
      usr$denominator <- mulmod(usr$denominator, _5, _2);
      _11 <- 2;
      _12 <- _2 - _11;
      tmp269,param_state_memory <@ usr$modexp(usr$denominator, _12, param_state_memory);
      usr$denominator <- tmp269;
      usr$res <- mulmod(usr$res, usr$denominator, _2);
      return (usr$res, param_state_memory);
      
      }
    }
  
  proc usr$prepareAggregatedCommitment(param_state_memory : mem): mem = {
    var param_state_memory, usr$aggregationChallenge, usr$firstDCoeff, usr$firstTCoeff, _1, _2, tmp377, _3, _4, _5, tmp378, _6, _7, usr$aggregatedOpeningAtZ, tmp379, _8, tmp380, _9, _10, _11, tmp381, _12, _13, tmp382, _14, _15, _16, tmp383, _17, _18, tmp384, _19, _20, tmp385, _21, tmp386, _22, _23, tmp387, _24, _25, _26, tmp388, _27, _28, tmp389, _29, _30, tmp390, _31, _32, tmp391, _33, tmp392, _34, _35, tmp393, _36, _37, _38, tmp394, _39, _40, tmp395, _41, _42, tmp396, _43, _44, tmp397, _45, _46, _47, tmp398, usr$copyPermutationCoeff, _48, _49, tmp399, _50, _51, tmp400, usr$aggregatedOpeningAtZOmega, _52, _53, tmp401, _54, _55, tmp402, _56, _57, tmp403, _58, _59, tmp404, _60, _61, tmp405, _62, _63, tmp406, _64, usr$u, tmp407, _65, tmp408, _66, tmp409, _67, tmp410, _68, usr$aggregatedValue, _69, _70, _71, _72, tmp411;
      {
      usr$aggregationChallenge <- 1;
      _1 <- 4288;
      tmp377 <@ MLoad(_1, param_state_memory);
      _2 <- tmp377;
      _3 <- 4480;
      param_state_memory <@ MStore(_3, _2, param_state_memory);
      _4 <- 4320;
      tmp378 <@ MLoad(_4, param_state_memory);
      _5 <- tmp378;
      _6 <- 4512;
      param_state_memory <@ MStore(_6, _5, param_state_memory);
      _7 <- 3072;
      tmp379 <@ MLoad(_7, param_state_memory);
      usr$aggregatedOpeningAtZ <- tmp379;
      _8 <- 4352;
      tmp380,param_state_memory <@ usr$pointAddIntoDest(_3, _8, _3, param_state_memory);
      _9 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _10 <- 4000;
      tmp381 <@ MLoad(_10, param_state_memory);
      _11 <- tmp381;
      usr$aggregationChallenge <- mulmod(usr$aggregationChallenge, _11, _9);
      _12 <- 3104;
      tmp382 <@ MLoad(_12, param_state_memory);
      _13 <- tmp382;
      _14 <- mulmod(usr$aggregationChallenge, _13, _9);
      usr$aggregatedOpeningAtZ <- addmod(usr$aggregatedOpeningAtZ, _14, _9);
      _15 <- 2560;
      _16 <- 1856;
      tmp383,param_state_memory <@ usr$updateAggregationChallenge(_16, _15, usr$aggregationChallenge, usr$aggregatedOpeningAtZ, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- tmp383;
      _17 <- 2592;
      _18 <- 1920;
      tmp384,param_state_memory <@ usr$updateAggregationChallenge(_18, _17, usr$aggregationChallenge, usr$aggregatedOpeningAtZ, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- tmp384;
      _19 <- 2624;
      _20 <- 1984;
      tmp385,param_state_memory <@ usr$updateAggregationChallenge(_20, _19, usr$aggregationChallenge, usr$aggregatedOpeningAtZ, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- tmp385;
      tmp386 <@ MLoad(_10, param_state_memory);
      _21 <- tmp386;
      usr$aggregationChallenge <- mulmod(usr$aggregationChallenge, _21, _9);
      usr$firstDCoeff <- usr$aggregationChallenge;
      _22 <- 2656;
      tmp387 <@ MLoad(_22, param_state_memory);
      _23 <- tmp387;
      _24 <- mulmod(usr$aggregationChallenge, _23, _9);
      usr$aggregatedOpeningAtZ <- addmod(usr$aggregatedOpeningAtZ, _24, _9);
      _25 <- 2720;
      _26 <- 1024;
      tmp388,param_state_memory <@ usr$updateAggregationChallenge(_26, _25, usr$aggregationChallenge, usr$aggregatedOpeningAtZ, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- tmp388;
      _27 <- 2752;
      _28 <- 1152;
      tmp389,param_state_memory <@ usr$updateAggregationChallenge(_28, _27, usr$aggregationChallenge, usr$aggregatedOpeningAtZ, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- tmp389;
      _29 <- 2784;
      _30 <- 1216;
      tmp390,param_state_memory <@ usr$updateAggregationChallenge(_30, _29, usr$aggregationChallenge, usr$aggregatedOpeningAtZ, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- tmp390;
      _31 <- 2816;
      _32 <- 1280;
      tmp391,param_state_memory <@ usr$updateAggregationChallenge(_32, _31, usr$aggregationChallenge, usr$aggregatedOpeningAtZ, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- tmp391;
      tmp392 <@ MLoad(_10, param_state_memory);
      _33 <- tmp392;
      usr$aggregationChallenge <- mulmod(usr$aggregationChallenge, _33, _9);
      usr$firstTCoeff <- usr$aggregationChallenge;
      _34 <- 2944;
      tmp393 <@ MLoad(_34, param_state_memory);
      _35 <- tmp393;
      _36 <- mulmod(usr$aggregationChallenge, _35, _9);
      usr$aggregatedOpeningAtZ <- addmod(usr$aggregatedOpeningAtZ, _36, _9);
      _37 <- 3008;
      _38 <- 1408;
      tmp394,param_state_memory <@ usr$updateAggregationChallenge(_38, _37, usr$aggregationChallenge, usr$aggregatedOpeningAtZ, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- tmp394;
      _39 <- 3040;
      _40 <- 1728;
      tmp395,param_state_memory <@ usr$updateAggregationChallenge(_40, _39, usr$aggregationChallenge, usr$aggregatedOpeningAtZ, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZ, <- tmp395;
      _41 <- 4608;
      param_state_memory <@ MStore(_41, usr$aggregatedOpeningAtZ, param_state_memory);
      tmp396 <@ MLoad(_10, param_state_memory);
      _42 <- tmp396;
      usr$aggregationChallenge <- mulmod(usr$aggregationChallenge, _42, _9);
      _43 <- 4032;
      tmp397 <@ MLoad(_43, param_state_memory);
      _44 <- tmp397;
      _45 <- mulmod(usr$aggregationChallenge, _44, _9);
      _46 <- 4928;
      tmp398 <@ MLoad(_46, param_state_memory);
      _47 <- tmp398;
      usr$copyPermutationCoeff <- addmod(_47, _45, _9);
      _48 <- 4544;
      _49 <- 2112;
      tmp399,param_state_memory <@ usr$pointMulIntoDest(_49, usr$copyPermutationCoeff, _48, param_state_memory);
      _50 <- 2848;
      tmp400 <@ MLoad(_50, param_state_memory);
      _51 <- tmp400;
      usr$aggregatedOpeningAtZOmega <- mulmod(_51, usr$aggregationChallenge, _9);
      _52 <- 2688;
      _53 <- 2048;
      tmp401,param_state_memory <@ usr$updateAggregationChallenge_105(_53, _52, usr$firstDCoeff, usr$aggregationChallenge, usr$aggregatedOpeningAtZOmega, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZOmega, <- tmp401;
      _54 <- 4992;
      tmp402 <@ MLoad(_54, param_state_memory);
      _55 <- tmp402;
      _56 <- 2880;
      _57 <- 2176;
      tmp403,param_state_memory <@ usr$updateAggregationChallenge_105(_57, _56, _55, usr$aggregationChallenge, usr$aggregatedOpeningAtZOmega, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZOmega, <- tmp403;
      _58 <- 4960;
      tmp404 <@ MLoad(_58, param_state_memory);
      _59 <- tmp404;
      _60 <- 2912;
      _61 <- 2240;
      tmp405,param_state_memory <@ usr$updateAggregationChallenge_105(_61, _60, _59, usr$aggregationChallenge, usr$aggregatedOpeningAtZOmega, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZOmega, <- tmp405;
      _62 <- 2976;
      _63 <- 4416;
      tmp406,param_state_memory <@ usr$updateAggregationChallenge_105(_63, _62, usr$firstTCoeff, usr$aggregationChallenge, usr$aggregatedOpeningAtZOmega, param_state_memory);
      usr$aggregationChallengeusr$aggregatedOpeningAtZOmega, <- tmp406;
      _64 <- 4640;
      param_state_memory <@ MStore(_64, usr$aggregatedOpeningAtZOmega, param_state_memory);
      tmp407 <@ MLoad(_43, param_state_memory);
      usr$u <- tmp407;
      _65 <- 4736;
      tmp408,param_state_memory <@ usr$pointAddIntoDest(_3, _48, _65, param_state_memory);
      tmp409 <@ MLoad(_41, param_state_memory);
      _66 <- tmp409;
      tmp410 <@ MLoad(_64, param_state_memory);
      _67 <- tmp410;
      _68 <- mulmod(_67, usr$u, _9);
      usr$aggregatedValue <- addmod(_68, _66, _9);
      _69 <- 1;
      _70 <- 4672;
      param_state_memory <@ MStore(_70, _69, param_state_memory);
      _71 <- 2;
      _72 <- 4704;
      param_state_memory <@ MStore(_72, _71, param_state_memory);
      tmp411,param_state_memory <@ usr$pointMulIntoDest(_70, usr$aggregatedValue, _70, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  proc revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc fun_verificationKeyHash(param_state_memory : mem): (uint256 * mem) = {
    var var_vkHash, param_state_memory, tmp47, usr$start, usr$end, _1, _2, usr$length, tmp48;
      {
       <@ Pop(zero_value_for_split_bytes32);
      tmp47,param_state_memory <@ fun_loadVerificationKey(param_state_memory);
      usr$start <- 512;
      usr$end <- 1792;
      _1 <- 32;
      _2 <- usr$end - usr$start;
      usr$length <- _2 + _1;
      tmp48 <@ Keccak256(usr$start, usr$length);
      var_vkHash <- tmp48;
      return (var_vkHash, param_state_memory);
      
      }
    }
  
  proc usr$prepareQueries(param_state_memory : mem): mem = {
    var param_state_memory, _1, usr$zInDomainSize, tmp350, usr$currentZ, _2, _3, tmp351, _4, _5, _6, tmp352, _7, _8, tmp353, _9, _10, tmp354, _11, tmp355, _12, usr$stateOpening0AtZ, tmp356, _13, usr$stateOpening1AtZ, tmp357, _14, usr$stateOpening2AtZ, tmp358, _15, usr$stateOpening3AtZ, tmp359, _16, tmp360, tmp361, tmp362, tmp363, _17, _18, tmp364, _19, _20, _21, tmp365, _22, _23, usr$eta, tmp366, usr$currentEta, _24, tmp367, _25, tmp368, _26, tmp369;
      {
      _1 <- 4192;
      tmp350 <@ MLoad(_1, param_state_memory);
      usr$zInDomainSize <- tmp350;
      usr$currentZ <- usr$zInDomainSize;
      _2 <- 2304;
      tmp351 <@ MLoad(_2, param_state_memory);
      _3 <- tmp351;
      _4 <- 4288;
      param_state_memory <@ MStore(_4, _3, param_state_memory);
      _5 <- 2336;
      tmp352 <@ MLoad(_5, param_state_memory);
      _6 <- tmp352;
      _7 <- 4320;
      param_state_memory <@ MStore(_7, _6, param_state_memory);
      _8 <- 2368;
      tmp353,param_state_memory <@ usr$pointMulAndAddIntoDest(_8, usr$zInDomainSize, _4, param_state_memory);
      _9 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      usr$currentZ <- mulmod(usr$zInDomainSize, usr$zInDomainSize, _9);
      _10 <- 2432;
      tmp354,param_state_memory <@ usr$pointMulAndAddIntoDest(_10, usr$currentZ, _4, param_state_memory);
      usr$currentZ <- mulmod(usr$currentZ, usr$zInDomainSize, _9);
      _11 <- 2496;
      tmp355,param_state_memory <@ usr$pointMulAndAddIntoDest(_11, usr$currentZ, _4, param_state_memory);
      _12 <- 2560;
      tmp356 <@ MLoad(_12, param_state_memory);
      usr$stateOpening0AtZ <- tmp356;
      _13 <- 2592;
      tmp357 <@ MLoad(_13, param_state_memory);
      usr$stateOpening1AtZ <- tmp357;
      _14 <- 2624;
      tmp358 <@ MLoad(_14, param_state_memory);
      usr$stateOpening2AtZ <- tmp358;
      _15 <- 2656;
      tmp359 <@ MLoad(_15, param_state_memory);
      usr$stateOpening3AtZ <- tmp359;
      _16 <- 4352;
      tmp360,param_state_memory <@ usr$mainGateLinearisationContributionWithV(_16, usr$stateOpening0AtZ, usr$stateOpening1AtZ, usr$stateOpening2AtZ, usr$stateOpening3AtZ, param_state_memory);
      tmp361,param_state_memory <@ usr$addAssignRescueCustomGateLinearisationContributionWithV(_16, usr$stateOpening0AtZ, usr$stateOpening1AtZ, usr$stateOpening2AtZ, usr$stateOpening3AtZ, param_state_memory);
      tmp362,param_state_memory <@ usr$addAssignPermutationLinearisationContributionWithV(_16, usr$stateOpening0AtZ, usr$stateOpening1AtZ, usr$stateOpening2AtZ, usr$stateOpening3AtZ, param_state_memory);
      tmp363,param_state_memory <@ usr$addAssignLookupLinearisationContributionWithV(_16, usr$stateOpening0AtZ, usr$stateOpening1AtZ, usr$stateOpening2AtZ, param_state_memory);
      _17 <- 1472;
      tmp364 <@ MLoad(_17, param_state_memory);
      _18 <- tmp364;
      _19 <- 4416;
      param_state_memory <@ MStore(_19, _18, param_state_memory);
      _20 <- 1504;
      tmp365 <@ MLoad(_20, param_state_memory);
      _21 <- tmp365;
      _22 <- 4448;
      param_state_memory <@ MStore(_22, _21, param_state_memory);
      _23 <- 3840;
      tmp366 <@ MLoad(_23, param_state_memory);
      usr$eta <- tmp366;
      usr$currentEta <- usr$eta;
      _24 <- 1536;
      tmp367,param_state_memory <@ usr$pointMulAndAddIntoDest(_24, usr$eta, _19, param_state_memory);
      usr$currentEta <- mulmod(usr$eta, usr$eta, _9);
      _25 <- 1600;
      tmp368,param_state_memory <@ usr$pointMulAndAddIntoDest(_25, usr$currentEta, _19, param_state_memory);
      usr$currentEta <- mulmod(usr$currentEta, usr$eta, _9);
      _26 <- 1664;
      tmp369,param_state_memory <@ usr$pointMulAndAddIntoDest(_26, usr$currentEta, _19, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  proc constructor_IVerifier(): unit = {
      {
      
      }
    }
  
  proc revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc abi_encode_bool_to_bool(value : uint256, pos : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp31;
      {
      tmp31 <@ cleanup_bool(value);
      _1 <- tmp31;
      param_state_memory <@ MStore(pos, _1, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  proc usr$addAssignRescueCustomGateLinearisationContributionWithV(usr$dest : uint256, usr$stateOpening0AtZ : uint256, usr$stateOpening1AtZ : uint256, usr$stateOpening2AtZ : uint256, usr$stateOpening3AtZ : uint256, param_state_memory : mem): mem = {
    var param_state_memory, usr$accumulator, usr$intermediateValue, _1, _2, _3, _4, tmp307, _5, _6, _7, tmp308, _8, _9, _10, tmp309, _11, _12, tmp310, _13, tmp311;
      {
      _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      usr$accumulator <- mulmod(usr$stateOpening0AtZ, usr$stateOpening0AtZ, _1);
      _2 <- _1 - usr$stateOpening1AtZ;
      usr$accumulator <- addmod(usr$accumulator, _2, _1);
      _3 <- 3520;
      tmp307 <@ MLoad(_3, param_state_memory);
      _4 <- tmp307;
      usr$accumulator <- mulmod(usr$accumulator, _4, _1);
      usr$intermediateValue <- mulmod(usr$stateOpening1AtZ, usr$stateOpening1AtZ, _1);
      _5 <- _1 - usr$stateOpening2AtZ;
      usr$intermediateValue <- addmod(usr$intermediateValue, _5, _1);
      _6 <- 3616;
      tmp308 <@ MLoad(_6, param_state_memory);
      _7 <- tmp308;
      usr$intermediateValue <- mulmod(usr$intermediateValue, _7, _1);
      usr$accumulator <- addmod(usr$accumulator, usr$intermediateValue, _1);
      usr$intermediateValue <- mulmod(usr$stateOpening2AtZ, usr$stateOpening0AtZ, _1);
      _8 <- _1 - usr$stateOpening3AtZ;
      usr$intermediateValue <- addmod(usr$intermediateValue, _8, _1);
      _9 <- 3648;
      tmp309 <@ MLoad(_9, param_state_memory);
      _10 <- tmp309;
      usr$intermediateValue <- mulmod(usr$intermediateValue, _10, _1);
      usr$accumulator <- addmod(usr$accumulator, usr$intermediateValue, _1);
      _11 <- 4000;
      tmp310 <@ MLoad(_11, param_state_memory);
      _12 <- tmp310;
      usr$accumulator <- mulmod(usr$accumulator, _12, _1);
      _13 <- 1088;
      tmp311,param_state_memory <@ usr$pointMulAndAddIntoDest(_13, usr$accumulator, usr$dest, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  proc BODY(): unit = {
    var zero_bool, tmp434, tmp435, tmp436, tmp437, tmp438, tmp439, tmp440, _1, _2, _3;
      {
      _1 <- 128;
      _2 <- 64;
       <@ MStore(_2, _1);
      _3 <- 4;
      tmp9 <@ CallDataSize();
      _4 <- tmp9;
      _5 <- lt(_4, _3);
      _6 <- iszero(_5);
      if (_6)
        {
        _7 <- 0;
        tmp10 <@ CallDataLoad(_7);
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
          ;
          
          }
        ;
        
        }
      ;
      tmp15 <@ revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74();
      
      }
    }
  
  proc usr$updateAggregationChallenge(usr$queriesCommitmentPoint : uint256, usr$valueAtZ : uint256, usr$curAggregationChallenge : uint256, usr$curAggregatedOpeningAtZ : uint256, param_state_memory : mem): (uint256 * uint256 * mem) = {
    var usr$newAggregationChallenge, usr$newAggregatedOpeningAtZ, param_state_memory, _1, _2, _3, tmp370, _4, tmp371, _5, tmp372, _6;
      {
      _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _2 <- 4000;
      tmp370 <@ MLoad(_2, param_state_memory);
      _3 <- tmp370;
      usr$newAggregationChallenge <- mulmod(usr$curAggregationChallenge, _3, _1);
      _4 <- 4480;
      tmp371,param_state_memory <@ usr$pointMulAndAddIntoDest(usr$queriesCommitmentPoint, usr$newAggregationChallenge, _4, param_state_memory);
      tmp372 <@ MLoad(usr$valueAtZ, param_state_memory);
      _5 <- tmp372;
      _6 <- mulmod(usr$newAggregationChallenge, _5, _1);
      usr$newAggregatedOpeningAtZ <- addmod(usr$curAggregatedOpeningAtZ, _6, _1);
      return (usr$newAggregationChallenge, usr$newAggregatedOpeningAtZ, param_state_memory);
      
      }
    }
  
  proc allocate_unbounded(param_state_memory : mem): uint256 = {
    var memPtr, _1, tmp7;
      {
      _1 <- 64;
      tmp7 <@ MLoad(_1, param_state_memory);
      memPtr <- tmp7;
      return memPtr;
      
      }
    }
  
  proc revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc usr$revertWithMessage(usr$len : uint256, usr$reason : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, _2, _3, _4, _5, _6, _7;
      {
      _1 <- 229 << 4594637;
      _2 <- 0;
      param_state_memory <@ MStore(_2, _1, param_state_memory);
      _3 <- 32;
      _4 <- 4;
      param_state_memory <@ MStore(_4, _3, param_state_memory);
      _5 <- 36;
      param_state_memory <@ MStore(_5, usr$len, param_state_memory);
      _6 <- 68;
      param_state_memory <@ MStore(_6, usr$reason, param_state_memory);
      _7 <- 100;
      return ();
      return param_state_memory;
      
      }
    }
  
  proc abi_decode(headStart : uint256, dataEnd : uint256): unit = {
    var _1, _2, _3, tmp38;
      {
      _1 <- 0;
      _2 <- dataEnd - headStart;
      _3 <- slt(_2, _1);
      if (_3)
        {
        tmp38 <@ revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b();
        
        }
      ;
      
      }
    }
  
  proc usr$initializeTranscript(param_state_memory : mem): mem = {
    var param_state_memory, _1, _2, tmp153, tmp154, _3, _4, tmp155, tmp156, _5, _6, tmp157, tmp158, _7, _8, tmp159, tmp160, _9, _10, tmp161, tmp162, _11, _12, tmp163, tmp164, _13, _14, tmp165, tmp166, _15, _16, tmp167, tmp168, _17, _18, tmp169, tmp170, _19, _20, tmp171, _21, _22, _23, tmp172, tmp173, _24, _25, tmp174, tmp175, _26, _27, tmp176, _28, _29, _30, tmp177, _31, _32, _33, tmp178, tmp179, _34, _35, tmp180, tmp181, _36, _37, tmp182, _38, _39, _40, tmp183, _41, _42, _43, tmp184, tmp185, _44, _45, tmp186, tmp187, _46, _47, tmp188, _48, _49, _50, tmp189, tmp190, _51, _52, tmp191, tmp192, _53, _54, tmp193, tmp194, _55, _56, tmp195, tmp196, _57, _58, tmp197, tmp198, _59, _60, tmp199, tmp200, _61, _62, tmp201, tmp202, _63, _64, tmp203, tmp204, _65, usr$z, tmp205, _66, _67, _68, tmp206, _69, _70, _71, tmp207, tmp208, _72, _73, tmp209, tmp210, _74, _75, tmp211, tmp212, _76, _77, tmp213, tmp214, _78, _79, tmp215, tmp216, _80, _81, tmp217, tmp218, _82, _83, tmp219, tmp220, _84, _85, tmp221, tmp222, _86, _87, tmp223, tmp224, _88, _89, tmp225, tmp226, _90, _91, tmp227, tmp228, _92, _93, tmp229, tmp230, _94, _95, tmp231, tmp232, _96, _97, tmp233, tmp234, _98, _99, tmp235, tmp236, _100, _101, tmp237, tmp238, _102, _103, tmp239, tmp240, _104, _105, tmp241, tmp242, _106, _107, tmp243, _108, _109, _110, tmp244, tmp245, _111, _112, tmp246, tmp247, _113, _114, tmp248, tmp249, _115, _116, tmp250, tmp251, _117, _118, tmp252, _119;
      {
      _1 <- 1824;
      tmp153 <@ MLoad(_1, param_state_memory);
      _2 <- tmp153;
      tmp154,param_state_memory <@ usr$updateTranscript(_2, param_state_memory);
      _3 <- 1856;
      tmp155 <@ MLoad(_3, param_state_memory);
      _4 <- tmp155;
      tmp156,param_state_memory <@ usr$updateTranscript(_4, param_state_memory);
      _5 <- 1888;
      tmp157 <@ MLoad(_5, param_state_memory);
      _6 <- tmp157;
      tmp158,param_state_memory <@ usr$updateTranscript(_6, param_state_memory);
      _7 <- 1920;
      tmp159 <@ MLoad(_7, param_state_memory);
      _8 <- tmp159;
      tmp160,param_state_memory <@ usr$updateTranscript(_8, param_state_memory);
      _9 <- 1952;
      tmp161 <@ MLoad(_9, param_state_memory);
      _10 <- tmp161;
      tmp162,param_state_memory <@ usr$updateTranscript(_10, param_state_memory);
      _11 <- 1984;
      tmp163 <@ MLoad(_11, param_state_memory);
      _12 <- tmp163;
      tmp164,param_state_memory <@ usr$updateTranscript(_12, param_state_memory);
      _13 <- 2016;
      tmp165 <@ MLoad(_13, param_state_memory);
      _14 <- tmp165;
      tmp166,param_state_memory <@ usr$updateTranscript(_14, param_state_memory);
      _15 <- 2048;
      tmp167 <@ MLoad(_15, param_state_memory);
      _16 <- tmp167;
      tmp168,param_state_memory <@ usr$updateTranscript(_16, param_state_memory);
      _17 <- 2080;
      tmp169 <@ MLoad(_17, param_state_memory);
      _18 <- tmp169;
      tmp170,param_state_memory <@ usr$updateTranscript(_18, param_state_memory);
      _19 <- 0;
      tmp171,param_state_memory <@ usr$getTranscriptChallenge(_19, param_state_memory);
      _20 <- tmp171;
      _21 <- 3840;
      param_state_memory <@ MStore(_21, _20, param_state_memory);
      _22 <- 2176;
      tmp172 <@ MLoad(_22, param_state_memory);
      _23 <- tmp172;
      tmp173,param_state_memory <@ usr$updateTranscript(_23, param_state_memory);
      _24 <- 2208;
      tmp174 <@ MLoad(_24, param_state_memory);
      _25 <- tmp174;
      tmp175,param_state_memory <@ usr$updateTranscript(_25, param_state_memory);
      _26 <- 1;
      tmp176,param_state_memory <@ usr$getTranscriptChallenge(_26, param_state_memory);
      _27 <- tmp176;
      _28 <- 3552;
      param_state_memory <@ MStore(_28, _27, param_state_memory);
      _29 <- 2;
      tmp177,param_state_memory <@ usr$getTranscriptChallenge(_29, param_state_memory);
      _30 <- tmp177;
      _31 <- 3584;
      param_state_memory <@ MStore(_31, _30, param_state_memory);
      _32 <- 2112;
      tmp178 <@ MLoad(_32, param_state_memory);
      _33 <- tmp178;
      tmp179,param_state_memory <@ usr$updateTranscript(_33, param_state_memory);
      _34 <- 2144;
      tmp180 <@ MLoad(_34, param_state_memory);
      _35 <- tmp180;
      tmp181,param_state_memory <@ usr$updateTranscript(_35, param_state_memory);
      _36 <- 3;
      tmp182,param_state_memory <@ usr$getTranscriptChallenge(_36, param_state_memory);
      _37 <- tmp182;
      _38 <- 3872;
      param_state_memory <@ MStore(_38, _37, param_state_memory);
      _39 <- 4;
      tmp183,param_state_memory <@ usr$getTranscriptChallenge(_39, param_state_memory);
      _40 <- tmp183;
      _41 <- 3904;
      param_state_memory <@ MStore(_41, _40, param_state_memory);
      _42 <- 2240;
      tmp184 <@ MLoad(_42, param_state_memory);
      _43 <- tmp184;
      tmp185,param_state_memory <@ usr$updateTranscript(_43, param_state_memory);
      _44 <- 2272;
      tmp186 <@ MLoad(_44, param_state_memory);
      _45 <- tmp186;
      tmp187,param_state_memory <@ usr$updateTranscript(_45, param_state_memory);
      _46 <- 5;
      tmp188,param_state_memory <@ usr$getTranscriptChallenge(_46, param_state_memory);
      _47 <- tmp188;
      _48 <- 3520;
      param_state_memory <@ MStore(_48, _47, param_state_memory);
      _49 <- 2304;
      tmp189 <@ MLoad(_49, param_state_memory);
      _50 <- tmp189;
      tmp190,param_state_memory <@ usr$updateTranscript(_50, param_state_memory);
      _51 <- 2336;
      tmp191 <@ MLoad(_51, param_state_memory);
      _52 <- tmp191;
      tmp192,param_state_memory <@ usr$updateTranscript(_52, param_state_memory);
      _53 <- 2368;
      tmp193 <@ MLoad(_53, param_state_memory);
      _54 <- tmp193;
      tmp194,param_state_memory <@ usr$updateTranscript(_54, param_state_memory);
      _55 <- 2400;
      tmp195 <@ MLoad(_55, param_state_memory);
      _56 <- tmp195;
      tmp196,param_state_memory <@ usr$updateTranscript(_56, param_state_memory);
      _57 <- 2432;
      tmp197 <@ MLoad(_57, param_state_memory);
      _58 <- tmp197;
      tmp198,param_state_memory <@ usr$updateTranscript(_58, param_state_memory);
      _59 <- 2464;
      tmp199 <@ MLoad(_59, param_state_memory);
      _60 <- tmp199;
      tmp200,param_state_memory <@ usr$updateTranscript(_60, param_state_memory);
      _61 <- 2496;
      tmp201 <@ MLoad(_61, param_state_memory);
      _62 <- tmp201;
      tmp202,param_state_memory <@ usr$updateTranscript(_62, param_state_memory);
      _63 <- 2528;
      tmp203 <@ MLoad(_63, param_state_memory);
      _64 <- tmp203;
      tmp204,param_state_memory <@ usr$updateTranscript(_64, param_state_memory);
      _65 <- 6;
      tmp205,param_state_memory <@ usr$getTranscriptChallenge(_65, param_state_memory);
      usr$z <- tmp205;
      _66 <- 4064;
      param_state_memory <@ MStore(_66, usr$z, param_state_memory);
      _67 <- 67108864;
      tmp206,param_state_memory <@ usr$modexp(usr$z, _67, param_state_memory);
      _68 <- tmp206;
      _69 <- 4192;
      param_state_memory <@ MStore(_69, _68, param_state_memory);
      _70 <- 3072;
      tmp207 <@ MLoad(_70, param_state_memory);
      _71 <- tmp207;
      tmp208,param_state_memory <@ usr$updateTranscript(_71, param_state_memory);
      _72 <- 2560;
      tmp209 <@ MLoad(_72, param_state_memory);
      _73 <- tmp209;
      tmp210,param_state_memory <@ usr$updateTranscript(_73, param_state_memory);
      _74 <- 2592;
      tmp211 <@ MLoad(_74, param_state_memory);
      _75 <- tmp211;
      tmp212,param_state_memory <@ usr$updateTranscript(_75, param_state_memory);
      _76 <- 2624;
      tmp213 <@ MLoad(_76, param_state_memory);
      _77 <- tmp213;
      tmp214,param_state_memory <@ usr$updateTranscript(_77, param_state_memory);
      _78 <- 2656;
      tmp215 <@ MLoad(_78, param_state_memory);
      _79 <- tmp215;
      tmp216,param_state_memory <@ usr$updateTranscript(_79, param_state_memory);
      _80 <- 2688;
      tmp217 <@ MLoad(_80, param_state_memory);
      _81 <- tmp217;
      tmp218,param_state_memory <@ usr$updateTranscript(_81, param_state_memory);
      _82 <- 2720;
      tmp219 <@ MLoad(_82, param_state_memory);
      _83 <- tmp219;
      tmp220,param_state_memory <@ usr$updateTranscript(_83, param_state_memory);
      _84 <- 2752;
      tmp221 <@ MLoad(_84, param_state_memory);
      _85 <- tmp221;
      tmp222,param_state_memory <@ usr$updateTranscript(_85, param_state_memory);
      _86 <- 2784;
      tmp223 <@ MLoad(_86, param_state_memory);
      _87 <- tmp223;
      tmp224,param_state_memory <@ usr$updateTranscript(_87, param_state_memory);
      _88 <- 2816;
      tmp225 <@ MLoad(_88, param_state_memory);
      _89 <- tmp225;
      tmp226,param_state_memory <@ usr$updateTranscript(_89, param_state_memory);
      _90 <- 2848;
      tmp227 <@ MLoad(_90, param_state_memory);
      _91 <- tmp227;
      tmp228,param_state_memory <@ usr$updateTranscript(_91, param_state_memory);
      _92 <- 2944;
      tmp229 <@ MLoad(_92, param_state_memory);
      _93 <- tmp229;
      tmp230,param_state_memory <@ usr$updateTranscript(_93, param_state_memory);
      _94 <- 3008;
      tmp231 <@ MLoad(_94, param_state_memory);
      _95 <- tmp231;
      tmp232,param_state_memory <@ usr$updateTranscript(_95, param_state_memory);
      _96 <- 3040;
      tmp233 <@ MLoad(_96, param_state_memory);
      _97 <- tmp233;
      tmp234,param_state_memory <@ usr$updateTranscript(_97, param_state_memory);
      _98 <- 2880;
      tmp235 <@ MLoad(_98, param_state_memory);
      _99 <- tmp235;
      tmp236,param_state_memory <@ usr$updateTranscript(_99, param_state_memory);
      _100 <- 2912;
      tmp237 <@ MLoad(_100, param_state_memory);
      _101 <- tmp237;
      tmp238,param_state_memory <@ usr$updateTranscript(_101, param_state_memory);
      _102 <- 2976;
      tmp239 <@ MLoad(_102, param_state_memory);
      _103 <- tmp239;
      tmp240,param_state_memory <@ usr$updateTranscript(_103, param_state_memory);
      _104 <- 3104;
      tmp241 <@ MLoad(_104, param_state_memory);
      _105 <- tmp241;
      tmp242,param_state_memory <@ usr$updateTranscript(_105, param_state_memory);
      _106 <- 7;
      tmp243,param_state_memory <@ usr$getTranscriptChallenge(_106, param_state_memory);
      _107 <- tmp243;
      _108 <- 4000;
      param_state_memory <@ MStore(_108, _107, param_state_memory);
      _109 <- 3136;
      tmp244 <@ MLoad(_109, param_state_memory);
      _110 <- tmp244;
      tmp245,param_state_memory <@ usr$updateTranscript(_110, param_state_memory);
      _111 <- 3168;
      tmp246 <@ MLoad(_111, param_state_memory);
      _112 <- tmp246;
      tmp247,param_state_memory <@ usr$updateTranscript(_112, param_state_memory);
      _113 <- 3200;
      tmp248 <@ MLoad(_113, param_state_memory);
      _114 <- tmp248;
      tmp249,param_state_memory <@ usr$updateTranscript(_114, param_state_memory);
      _115 <- 3232;
      tmp250 <@ MLoad(_115, param_state_memory);
      _116 <- tmp250;
      tmp251,param_state_memory <@ usr$updateTranscript(_116, param_state_memory);
      _117 <- 8;
      tmp252,param_state_memory <@ usr$getTranscriptChallenge(_117, param_state_memory);
      _118 <- tmp252;
      _119 <- 4032;
      param_state_memory <@ MStore(_119, _118, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  proc usr$permutationQuotientContribution(param_state_memory : mem): uint256 = {
    var usr$res, _1, _2, _3, tmp270, _4, _5, tmp271, _6, usr$gamma, tmp272, _7, usr$beta, tmp273, usr$factorMultiplier, _8, _9, tmp274, _10, _11, tmp275, _12, _13, tmp276, _14, _15, tmp277, _16, _17, tmp278, _18, _19, tmp279, _20, _21, tmp280, _22, _23, usr$l0AtZ, tmp281, _24, _25, tmp282, _26;
      {
      _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _2 <- 2848;
      tmp270 <@ MLoad(_2, param_state_memory);
      _3 <- tmp270;
      _4 <- 3680;
      tmp271 <@ MLoad(_4, param_state_memory);
      _5 <- tmp271;
      usr$res <- mulmod(_5, _3, _1);
      _6 <- 3584;
      tmp272 <@ MLoad(_6, param_state_memory);
      usr$gamma <- tmp272;
      _7 <- 3552;
      tmp273 <@ MLoad(_7, param_state_memory);
      usr$beta <- tmp273;
      _8 <- 2752;
      tmp274 <@ MLoad(_8, param_state_memory);
      _9 <- tmp274;
      usr$factorMultiplier <- mulmod(_9, usr$beta, _1);
      usr$factorMultiplier <- addmod(usr$factorMultiplier, usr$gamma, _1);
      _10 <- 2560;
      tmp275 <@ MLoad(_10, param_state_memory);
      _11 <- tmp275;
      usr$factorMultiplier <- addmod(usr$factorMultiplier, _11, _1);
      usr$res <- mulmod(usr$res, usr$factorMultiplier, _1);
      _12 <- 2784;
      tmp276 <@ MLoad(_12, param_state_memory);
      _13 <- tmp276;
      usr$factorMultiplier <- mulmod(_13, usr$beta, _1);
      usr$factorMultiplier <- addmod(usr$factorMultiplier, usr$gamma, _1);
      _14 <- 2592;
      tmp277 <@ MLoad(_14, param_state_memory);
      _15 <- tmp277;
      usr$factorMultiplier <- addmod(usr$factorMultiplier, _15, _1);
      usr$res <- mulmod(usr$res, usr$factorMultiplier, _1);
      _16 <- 2816;
      tmp278 <@ MLoad(_16, param_state_memory);
      _17 <- tmp278;
      usr$factorMultiplier <- mulmod(_17, usr$beta, _1);
      usr$factorMultiplier <- addmod(usr$factorMultiplier, usr$gamma, _1);
      _18 <- 2624;
      tmp279 <@ MLoad(_18, param_state_memory);
      _19 <- tmp279;
      usr$factorMultiplier <- addmod(usr$factorMultiplier, _19, _1);
      usr$res <- mulmod(usr$res, usr$factorMultiplier, _1);
      _20 <- 2656;
      tmp280 <@ MLoad(_20, param_state_memory);
      _21 <- tmp280;
      _22 <- addmod(_21, usr$gamma, _1);
      usr$res <- mulmod(usr$res, _22, _1);
      usr$res <- _1 - usr$res;
      _23 <- 4128;
      tmp281 <@ MLoad(_23, param_state_memory);
      usr$l0AtZ <- tmp281;
      _24 <- 3712;
      tmp282 <@ MLoad(_24, param_state_memory);
      _25 <- tmp282;
      usr$l0AtZ <- mulmod(usr$l0AtZ, _25, _1);
      _26 <- _1 - usr$l0AtZ;
      usr$res <- addmod(usr$res, _26, _1);
      return usr$res;
      
      }
    }
  
  proc abi_encode_bytes32_to_bytes32(value : uint256, pos : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1;
      {
      _1 <- cleanup_bytes32(value);
      param_state_memory <@ MStore(pos, _1, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  proc allocate_unbounded(param_state_memory : mem): uint256 = {
    var memPtr, _1, tmp16;
      {
      _1 <- 64;
      tmp16 <@ MLoad(_1, param_state_memory);
      memPtr <- tmp16;
      return memPtr;
      
      }
    }
  
  proc usr$loadProof(param_state_memory : mem): mem = {
    var param_state_memory, _1, usr$offset, tmp95, _2, usr$publicInputLengthInWords, tmp96, _3, usr$isValid, _4, _5, _6, _7, tmp97, _8, _9, tmp98, _10, usr$proofLengthInWords, tmp99, _11, _12, _13, _14, _15, tmp100, usr$x, _16, _17, _18, tmp101, usr$y, usr$xx, _19, _20, _21, _22, _23, _24, _25, _26, _27, _28, tmp102, usr$x_1, _29, _30, _31, tmp103, usr$y_1, usr$xx_1, _32, _33, _34, _35, _36, _37, _38, _39, _40, tmp104, usr$x_2, _41, _42, _43, tmp105, usr$y_2, usr$xx_2, _44, _45, _46, _47, _48, _49, _50, _51, _52, tmp106, usr$x_3, _53, _54, _55, tmp107, usr$y_3, usr$xx_3, _56, _57, _58, _59, _60, _61, _62, _63, _64, tmp108, usr$x_4, _65, _66, _67, tmp109, usr$y_4, usr$xx_4, _68, _69, _70, _71, _72, _73, _74, _75, _76, tmp110, usr$x_5, _77, _78, _79, tmp111, usr$y_5, usr$xx_5, _80, _81, _82, _83, _84, _85, _86, _87, _88, tmp112, usr$x_6, _89, _90, _91, tmp113, usr$y_6, usr$xx_6, _92, _93, _94, _95, _96, _97, _98, _99, _100, tmp114, usr$x_7, _101, _102, _103, tmp115, usr$y_7, usr$xx_7, _104, _105, _106, _107, _108, _109, _110, _111, _112, tmp116, usr$x_8, _113, _114, _115, tmp117, usr$y_8, usr$xx_8, _116, _117, _118, _119, _120, _121, _122, _123, _124, tmp118, usr$x_9, _125, _126, _127, tmp119, usr$y_9, usr$xx_9, _128, _129, _130, _131, _132, _133, _134, _135, _136, tmp120, usr$x_10, _137, _138, _139, tmp121, usr$y_10, usr$xx_10, _140, _141, _142, _143, _144, _145, _146, _147, _148, _149, tmp122, _150, _151, _152, _153, _154, tmp123, _155, _156, _157, _158, _159, tmp124, _160, _161, _162, _163, _164, tmp125, _165, _166, _167, _168, _169, tmp126, _170, _171, _172, _173, _174, tmp127, _175, _176, _177, _178, _179, tmp128, _180, _181, _182, _183, _184, tmp129, _185, _186, _187, _188, _189, tmp130, _190, _191, _192, _193, _194, tmp131, _195, _196, _197, _198, _199, tmp132, _200, _201, _202, _203, _204, tmp133, _205, _206, _207, _208, _209, tmp134, _210, _211, _212, _213, _214, tmp135, _215, _216, _217, _218, _219, tmp136, _220, _221, _222, _223, _224, tmp137, _225, _226, _227, _228, _229, tmp138, _230, _231, _232, _233, _234, tmp139, _235, _236, _237, _238, _239, tmp140, usr$x_11, _240, _241, _242, tmp141, usr$y_11, usr$xx_11, _243, _244, _245, _246, _247, _248, _249, _250, _251, tmp142, usr$x_12, _252, _253, _254, tmp143, usr$y_12, usr$xx_12, _255, _256, _257, _258, _259, _260, tmp144, _261, usr$recursiveProofLengthInWords, tmp145, _262, _263, tmp146, _264, _265, _266, _267, tmp148, usr$x_13, _268, _269, tmp149, usr$y_13, usr$xx_13, _270, _271, _272, _273, _274, _275, _276, _277, tmp150, usr$x_14, _278, _279, tmp151, usr$y_14, usr$xx_14, _280, _281, _282, _283, _284, _285, _286, _287, _288, tmp152;
      {
      _1 <- 4;
      tmp95 <@ CallDataLoad(_1);
      usr$offset <- tmp95;
      _2 <- usr$offset + _1;
      tmp96 <@ CallDataLoad(_2);
      usr$publicInputLengthInWords <- tmp96;
      _3 <- 1;
      usr$isValid <- usr$publicInputLengthInWords = _3;
      _4 <- 253 << 1 - 1;
      _5 <- 36;
      _6 <- usr$offset + _5;
      tmp97 <@ CallDataLoad(_6);
      _7 <- tmp97;
      _8 <- _7 /\ _4;
      _9 <- 1824;
      param_state_memory <@ MStore(_9, _8, param_state_memory);
      tmp98 <@ CallDataLoad(_5);
      usr$offset <- tmp98;
      _10 <- usr$offset + _1;
      tmp99 <@ CallDataLoad(_10);
      usr$proofLengthInWords <- tmp99;
      _11 <- 44;
      _12 <- usr$proofLengthInWords = _11;
      usr$isValid <- _12 /\ usr$isValid;
      _13 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
      _14 <- usr$offset + _5;
      tmp100 <@ CallDataLoad(_14);
      _15 <- tmp100;
      usr$x <- _15 % _13;
      _16 <- 68;
      _17 <- usr$offset + _16;
      tmp101 <@ CallDataLoad(_17);
      _18 <- tmp101;
      usr$y <- _18 % _13;
      usr$xx <- mulmod(usr$x, usr$x, _13);
      _19 <- 3;
      _20 <- mulmod(usr$x, usr$xx, _13);
      _21 <- addmod(_20, _19, _13);
      _22 <- mulmod(usr$y, usr$y, _13);
      _23 <- _22 = _21;
      usr$isValid <- _23 /\ usr$isValid;
      _24 <- 1856;
      param_state_memory <@ MStore(_24, usr$x, param_state_memory);
      _25 <- 1888;
      param_state_memory <@ MStore(_25, usr$y, param_state_memory);
      _26 <- 100;
      _27 <- usr$offset + _26;
      tmp102 <@ CallDataLoad(_27);
      _28 <- tmp102;
      usr$x_1 <- _28 % _13;
      _29 <- 132;
      _30 <- usr$offset + _29;
      tmp103 <@ CallDataLoad(_30);
      _31 <- tmp103;
      usr$y_1 <- _31 % _13;
      usr$xx_1 <- mulmod(usr$x_1, usr$x_1, _13);
      _32 <- mulmod(usr$x_1, usr$xx_1, _13);
      _33 <- addmod(_32, _19, _13);
      _34 <- mulmod(usr$y_1, usr$y_1, _13);
      _35 <- _34 = _33;
      usr$isValid <- _35 /\ usr$isValid;
      _36 <- 1920;
      param_state_memory <@ MStore(_36, usr$x_1, param_state_memory);
      _37 <- 1952;
      param_state_memory <@ MStore(_37, usr$y_1, param_state_memory);
      _38 <- 164;
      _39 <- usr$offset + _38;
      tmp104 <@ CallDataLoad(_39);
      _40 <- tmp104;
      usr$x_2 <- _40 % _13;
      _41 <- 196;
      _42 <- usr$offset + _41;
      tmp105 <@ CallDataLoad(_42);
      _43 <- tmp105;
      usr$y_2 <- _43 % _13;
      usr$xx_2 <- mulmod(usr$x_2, usr$x_2, _13);
      _44 <- mulmod(usr$x_2, usr$xx_2, _13);
      _45 <- addmod(_44, _19, _13);
      _46 <- mulmod(usr$y_2, usr$y_2, _13);
      _47 <- _46 = _45;
      usr$isValid <- _47 /\ usr$isValid;
      _48 <- 1984;
      param_state_memory <@ MStore(_48, usr$x_2, param_state_memory);
      _49 <- 2016;
      param_state_memory <@ MStore(_49, usr$y_2, param_state_memory);
      _50 <- 228;
      _51 <- usr$offset + _50;
      tmp106 <@ CallDataLoad(_51);
      _52 <- tmp106;
      usr$x_3 <- _52 % _13;
      _53 <- 260;
      _54 <- usr$offset + _53;
      tmp107 <@ CallDataLoad(_54);
      _55 <- tmp107;
      usr$y_3 <- _55 % _13;
      usr$xx_3 <- mulmod(usr$x_3, usr$x_3, _13);
      _56 <- mulmod(usr$x_3, usr$xx_3, _13);
      _57 <- addmod(_56, _19, _13);
      _58 <- mulmod(usr$y_3, usr$y_3, _13);
      _59 <- _58 = _57;
      usr$isValid <- _59 /\ usr$isValid;
      _60 <- 2048;
      param_state_memory <@ MStore(_60, usr$x_3, param_state_memory);
      _61 <- 2080;
      param_state_memory <@ MStore(_61, usr$y_3, param_state_memory);
      _62 <- 292;
      _63 <- usr$offset + _62;
      tmp108 <@ CallDataLoad(_63);
      _64 <- tmp108;
      usr$x_4 <- _64 % _13;
      _65 <- 324;
      _66 <- usr$offset + _65;
      tmp109 <@ CallDataLoad(_66);
      _67 <- tmp109;
      usr$y_4 <- _67 % _13;
      usr$xx_4 <- mulmod(usr$x_4, usr$x_4, _13);
      _68 <- mulmod(usr$x_4, usr$xx_4, _13);
      _69 <- addmod(_68, _19, _13);
      _70 <- mulmod(usr$y_4, usr$y_4, _13);
      _71 <- _70 = _69;
      usr$isValid <- _71 /\ usr$isValid;
      _72 <- 2112;
      param_state_memory <@ MStore(_72, usr$x_4, param_state_memory);
      _73 <- 2144;
      param_state_memory <@ MStore(_73, usr$y_4, param_state_memory);
      _74 <- 356;
      _75 <- usr$offset + _74;
      tmp110 <@ CallDataLoad(_75);
      _76 <- tmp110;
      usr$x_5 <- _76 % _13;
      _77 <- 388;
      _78 <- usr$offset + _77;
      tmp111 <@ CallDataLoad(_78);
      _79 <- tmp111;
      usr$y_5 <- _79 % _13;
      usr$xx_5 <- mulmod(usr$x_5, usr$x_5, _13);
      _80 <- mulmod(usr$x_5, usr$xx_5, _13);
      _81 <- addmod(_80, _19, _13);
      _82 <- mulmod(usr$y_5, usr$y_5, _13);
      _83 <- _82 = _81;
      usr$isValid <- _83 /\ usr$isValid;
      _84 <- 2176;
      param_state_memory <@ MStore(_84, usr$x_5, param_state_memory);
      _85 <- 2208;
      param_state_memory <@ MStore(_85, usr$y_5, param_state_memory);
      _86 <- 420;
      _87 <- usr$offset + _86;
      tmp112 <@ CallDataLoad(_87);
      _88 <- tmp112;
      usr$x_6 <- _88 % _13;
      _89 <- 452;
      _90 <- usr$offset + _89;
      tmp113 <@ CallDataLoad(_90);
      _91 <- tmp113;
      usr$y_6 <- _91 % _13;
      usr$xx_6 <- mulmod(usr$x_6, usr$x_6, _13);
      _92 <- mulmod(usr$x_6, usr$xx_6, _13);
      _93 <- addmod(_92, _19, _13);
      _94 <- mulmod(usr$y_6, usr$y_6, _13);
      _95 <- _94 = _93;
      usr$isValid <- _95 /\ usr$isValid;
      _96 <- 2240;
      param_state_memory <@ MStore(_96, usr$x_6, param_state_memory);
      _97 <- 2272;
      param_state_memory <@ MStore(_97, usr$y_6, param_state_memory);
      _98 <- 484;
      _99 <- usr$offset + _98;
      tmp114 <@ CallDataLoad(_99);
      _100 <- tmp114;
      usr$x_7 <- _100 % _13;
      _101 <- 516;
      _102 <- usr$offset + _101;
      tmp115 <@ CallDataLoad(_102);
      _103 <- tmp115;
      usr$y_7 <- _103 % _13;
      usr$xx_7 <- mulmod(usr$x_7, usr$x_7, _13);
      _104 <- mulmod(usr$x_7, usr$xx_7, _13);
      _105 <- addmod(_104, _19, _13);
      _106 <- mulmod(usr$y_7, usr$y_7, _13);
      _107 <- _106 = _105;
      usr$isValid <- _107 /\ usr$isValid;
      _108 <- 2304;
      param_state_memory <@ MStore(_108, usr$x_7, param_state_memory);
      _109 <- 2336;
      param_state_memory <@ MStore(_109, usr$y_7, param_state_memory);
      _110 <- 548;
      _111 <- usr$offset + _110;
      tmp116 <@ CallDataLoad(_111);
      _112 <- tmp116;
      usr$x_8 <- _112 % _13;
      _113 <- 580;
      _114 <- usr$offset + _113;
      tmp117 <@ CallDataLoad(_114);
      _115 <- tmp117;
      usr$y_8 <- _115 % _13;
      usr$xx_8 <- mulmod(usr$x_8, usr$x_8, _13);
      _116 <- mulmod(usr$x_8, usr$xx_8, _13);
      _117 <- addmod(_116, _19, _13);
      _118 <- mulmod(usr$y_8, usr$y_8, _13);
      _119 <- _118 = _117;
      usr$isValid <- _119 /\ usr$isValid;
      _120 <- 2368;
      param_state_memory <@ MStore(_120, usr$x_8, param_state_memory);
      _121 <- 2400;
      param_state_memory <@ MStore(_121, usr$y_8, param_state_memory);
      _122 <- 612;
      _123 <- usr$offset + _122;
      tmp118 <@ CallDataLoad(_123);
      _124 <- tmp118;
      usr$x_9 <- _124 % _13;
      _125 <- 644;
      _126 <- usr$offset + _125;
      tmp119 <@ CallDataLoad(_126);
      _127 <- tmp119;
      usr$y_9 <- _127 % _13;
      usr$xx_9 <- mulmod(usr$x_9, usr$x_9, _13);
      _128 <- mulmod(usr$x_9, usr$xx_9, _13);
      _129 <- addmod(_128, _19, _13);
      _130 <- mulmod(usr$y_9, usr$y_9, _13);
      _131 <- _130 = _129;
      usr$isValid <- _131 /\ usr$isValid;
      _132 <- 2432;
      param_state_memory <@ MStore(_132, usr$x_9, param_state_memory);
      _133 <- 2464;
      param_state_memory <@ MStore(_133, usr$y_9, param_state_memory);
      _134 <- 676;
      _135 <- usr$offset + _134;
      tmp120 <@ CallDataLoad(_135);
      _136 <- tmp120;
      usr$x_10 <- _136 % _13;
      _137 <- 708;
      _138 <- usr$offset + _137;
      tmp121 <@ CallDataLoad(_138);
      _139 <- tmp121;
      usr$y_10 <- _139 % _13;
      usr$xx_10 <- mulmod(usr$x_10, usr$x_10, _13);
      _140 <- mulmod(usr$x_10, usr$xx_10, _13);
      _141 <- addmod(_140, _19, _13);
      _142 <- mulmod(usr$y_10, usr$y_10, _13);
      _143 <- _142 = _141;
      usr$isValid <- _143 /\ usr$isValid;
      _144 <- 2496;
      param_state_memory <@ MStore(_144, usr$x_10, param_state_memory);
      _145 <- 2528;
      param_state_memory <@ MStore(_145, usr$y_10, param_state_memory);
      _146 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _147 <- 740;
      _148 <- usr$offset + _147;
      tmp122 <@ CallDataLoad(_148);
      _149 <- tmp122;
      _150 <- _149 % _146;
      _151 <- 2560;
      param_state_memory <@ MStore(_151, _150, param_state_memory);
      _152 <- 772;
      _153 <- usr$offset + _152;
      tmp123 <@ CallDataLoad(_153);
      _154 <- tmp123;
      _155 <- _154 % _146;
      _156 <- 2592;
      param_state_memory <@ MStore(_156, _155, param_state_memory);
      _157 <- 804;
      _158 <- usr$offset + _157;
      tmp124 <@ CallDataLoad(_158);
      _159 <- tmp124;
      _160 <- _159 % _146;
      _161 <- 2624;
      param_state_memory <@ MStore(_161, _160, param_state_memory);
      _162 <- 836;
      _163 <- usr$offset + _162;
      tmp125 <@ CallDataLoad(_163);
      _164 <- tmp125;
      _165 <- _164 % _146;
      _166 <- 2656;
      param_state_memory <@ MStore(_166, _165, param_state_memory);
      _167 <- 868;
      _168 <- usr$offset + _167;
      tmp126 <@ CallDataLoad(_168);
      _169 <- tmp126;
      _170 <- _169 % _146;
      _171 <- 2688;
      param_state_memory <@ MStore(_171, _170, param_state_memory);
      _172 <- 900;
      _173 <- usr$offset + _172;
      tmp127 <@ CallDataLoad(_173);
      _174 <- tmp127;
      _175 <- _174 % _146;
      _176 <- 2720;
      param_state_memory <@ MStore(_176, _175, param_state_memory);
      _177 <- 932;
      _178 <- usr$offset + _177;
      tmp128 <@ CallDataLoad(_178);
      _179 <- tmp128;
      _180 <- _179 % _146;
      _181 <- 2752;
      param_state_memory <@ MStore(_181, _180, param_state_memory);
      _182 <- 964;
      _183 <- usr$offset + _182;
      tmp129 <@ CallDataLoad(_183);
      _184 <- tmp129;
      _185 <- _184 % _146;
      _186 <- 2784;
      param_state_memory <@ MStore(_186, _185, param_state_memory);
      _187 <- 996;
      _188 <- usr$offset + _187;
      tmp130 <@ CallDataLoad(_188);
      _189 <- tmp130;
      _190 <- _189 % _146;
      _191 <- 2816;
      param_state_memory <@ MStore(_191, _190, param_state_memory);
      _192 <- 1028;
      _193 <- usr$offset + _192;
      tmp131 <@ CallDataLoad(_193);
      _194 <- tmp131;
      _195 <- _194 % _146;
      _196 <- 2848;
      param_state_memory <@ MStore(_196, _195, param_state_memory);
      _197 <- 1060;
      _198 <- usr$offset + _197;
      tmp132 <@ CallDataLoad(_198);
      _199 <- tmp132;
      _200 <- _199 % _146;
      _201 <- 2880;
      param_state_memory <@ MStore(_201, _200, param_state_memory);
      _202 <- 1092;
      _203 <- usr$offset + _202;
      tmp133 <@ CallDataLoad(_203);
      _204 <- tmp133;
      _205 <- _204 % _146;
      _206 <- 2912;
      param_state_memory <@ MStore(_206, _205, param_state_memory);
      _207 <- 1124;
      _208 <- usr$offset + _207;
      tmp134 <@ CallDataLoad(_208);
      _209 <- tmp134;
      _210 <- _209 % _146;
      _211 <- 2944;
      param_state_memory <@ MStore(_211, _210, param_state_memory);
      _212 <- 1156;
      _213 <- usr$offset + _212;
      tmp135 <@ CallDataLoad(_213);
      _214 <- tmp135;
      _215 <- _214 % _146;
      _216 <- 2976;
      param_state_memory <@ MStore(_216, _215, param_state_memory);
      _217 <- 1188;
      _218 <- usr$offset + _217;
      tmp136 <@ CallDataLoad(_218);
      _219 <- tmp136;
      _220 <- _219 % _146;
      _221 <- 3008;
      param_state_memory <@ MStore(_221, _220, param_state_memory);
      _222 <- 1220;
      _223 <- usr$offset + _222;
      tmp137 <@ CallDataLoad(_223);
      _224 <- tmp137;
      _225 <- _224 % _146;
      _226 <- 3040;
      param_state_memory <@ MStore(_226, _225, param_state_memory);
      _227 <- 1252;
      _228 <- usr$offset + _227;
      tmp138 <@ CallDataLoad(_228);
      _229 <- tmp138;
      _230 <- _229 % _146;
      _231 <- 3072;
      param_state_memory <@ MStore(_231, _230, param_state_memory);
      _232 <- 1284;
      _233 <- usr$offset + _232;
      tmp139 <@ CallDataLoad(_233);
      _234 <- tmp139;
      _235 <- _234 % _146;
      _236 <- 3104;
      param_state_memory <@ MStore(_236, _235, param_state_memory);
      _237 <- 1316;
      _238 <- usr$offset + _237;
      tmp140 <@ CallDataLoad(_238);
      _239 <- tmp140;
      usr$x_11 <- _239 % _13;
      _240 <- 1348;
      _241 <- usr$offset + _240;
      tmp141 <@ CallDataLoad(_241);
      _242 <- tmp141;
      usr$y_11 <- _242 % _13;
      usr$xx_11 <- mulmod(usr$x_11, usr$x_11, _13);
      _243 <- mulmod(usr$x_11, usr$xx_11, _13);
      _244 <- addmod(_243, _19, _13);
      _245 <- mulmod(usr$y_11, usr$y_11, _13);
      _246 <- _245 = _244;
      usr$isValid <- _246 /\ usr$isValid;
      _247 <- 3136;
      param_state_memory <@ MStore(_247, usr$x_11, param_state_memory);
      _248 <- 3168;
      param_state_memory <@ MStore(_248, usr$y_11, param_state_memory);
      _249 <- 1380;
      _250 <- usr$offset + _249;
      tmp142 <@ CallDataLoad(_250);
      _251 <- tmp142;
      usr$x_12 <- _251 % _13;
      _252 <- 1412;
      _253 <- usr$offset + _252;
      tmp143 <@ CallDataLoad(_253);
      _254 <- tmp143;
      usr$y_12 <- _254 % _13;
      usr$xx_12 <- mulmod(usr$x_12, usr$x_12, _13);
      _255 <- mulmod(usr$x_12, usr$xx_12, _13);
      _256 <- addmod(_255, _19, _13);
      _257 <- mulmod(usr$y_12, usr$y_12, _13);
      _258 <- _257 = _256;
      usr$isValid <- _258 /\ usr$isValid;
      _259 <- 3200;
      param_state_memory <@ MStore(_259, usr$x_12, param_state_memory);
      _260 <- 3232;
      param_state_memory <@ MStore(_260, usr$y_12, param_state_memory);
      tmp144 <@ CallDataLoad(_16);
      usr$offset <- tmp144;
      _261 <- usr$offset + _1;
      tmp145 <@ CallDataLoad(_261);
      usr$recursiveProofLengthInWords <- tmp145;
      _262 <- 1792;
      tmp146 <@ MLoad(_262, param_state_memory);
      _263 <- tmp146;
      tmp147 <- _263;
      if (tmp147 = 0)
        {
        _264 <- iszero(usr$recursiveProofLengthInWords);
        usr$isValid <- _264 /\ usr$isValid;
        
        }
      
      else {
        _265 <- usr$recursiveProofLengthInWords = _1;
        usr$isValid <- _265 /\ usr$isValid;
        _266 <- usr$offset + _5;
        tmp148 <@ CallDataLoad(_266);
        _267 <- tmp148;
        usr$x_13 <- _267 % _13;
        _268 <- usr$offset + _16;
        tmp149 <@ CallDataLoad(_268);
        _269 <- tmp149;
        usr$y_13 <- _269 % _13;
        usr$xx_13 <- mulmod(usr$x_13, usr$x_13, _13);
        _270 <- mulmod(usr$x_13, usr$xx_13, _13);
        _271 <- addmod(_270, _19, _13);
        _272 <- mulmod(usr$y_13, usr$y_13, _13);
        _273 <- _272 = _271;
        usr$isValid <- _273 /\ usr$isValid;
        _274 <- 3264;
        param_state_memory <@ MStore(_274, usr$x_13, param_state_memory);
        _275 <- 3296;
        param_state_memory <@ MStore(_275, usr$y_13, param_state_memory);
        _276 <- usr$offset + _26;
        tmp150 <@ CallDataLoad(_276);
        _277 <- tmp150;
        usr$x_14 <- _277 % _13;
        _278 <- usr$offset + _29;
        tmp151 <@ CallDataLoad(_278);
        _279 <- tmp151;
        usr$y_14 <- _279 % _13;
        usr$xx_14 <- mulmod(usr$x_14, usr$x_14, _13);
        _280 <- mulmod(usr$x_14, usr$xx_14, _13);
        _281 <- addmod(_280, _19, _13);
        _282 <- mulmod(usr$y_14, usr$y_14, _13);
        _283 <- _282 = _281;
        usr$isValid <- _283 /\ usr$isValid;
        _284 <- 3328;
        param_state_memory <@ MStore(_284, usr$x_14, param_state_memory);
        _285 <- 3360;
        param_state_memory <@ MStore(_285, usr$y_14, param_state_memory);
        
        }
      ;
      _286 <- iszero(usr$isValid);
      if (_286)
        {
        _287 <- "loadProof: Proof is invalid";
        _288 <- 27;
        tmp152,param_state_memory <@ usr$revertWithMessage(_288, _287, param_state_memory);
        
        }
      ;
      return param_state_memory;
      
      }
    }
  
  proc usr$pointAddIntoDest(usr$p1 : uint256, usr$p2 : uint256, usr$dest : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp58, _2, _3, _4, _5, tmp59, _6, tmp60, _7, _8, _9, tmp61, _10, _11, _12, _13, tmp62, _14, tmp63, _15, _16, _17, tmp64;
      {
      tmp58 <@ MLoad(usr$p1, param_state_memory);
      _1 <- tmp58;
      _2 <- 0;
      param_state_memory <@ MStore(_2, _1, param_state_memory);
      _3 <- 32;
      _4 <- usr$p1 + _3;
      tmp59 <@ MLoad(_4, param_state_memory);
      _5 <- tmp59;
      param_state_memory <@ MStore(_3, _5, param_state_memory);
      tmp60 <@ MLoad(usr$p2, param_state_memory);
      _6 <- tmp60;
      _7 <- 64;
      param_state_memory <@ MStore(_7, _6, param_state_memory);
      _8 <- usr$p2 + _3;
      tmp61 <@ MLoad(_8, param_state_memory);
      _9 <- tmp61;
      _10 <- 96;
      param_state_memory <@ MStore(_10, _9, param_state_memory);
      _11 <- 128;
      _12 <- 6;
      tmp62 <@ Gas();
      _13 <- tmp62;
      tmp63 <@ StaticCall(_13, _12, _2, _11, usr$dest, _7);
      _14 <- tmp63;
      _15 <- iszero(_14);
      if (_15)
        {
        _16 <- "pointAddIntoDest: ecAdd failed";
        _17 <- 30;
        tmp64,param_state_memory <@ usr$revertWithMessage(_17, _16, param_state_memory);
        
        }
      ;
      return param_state_memory;
      
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
  
  proc constructor_Verifier(): unit = {
    var tmp8;
      {
      tmp8 <@ constructor_IVerifier();
      
      }
    }
  
  proc fun_verify(var__offset : uint256, var_length : uint256, var_offset : uint256, var__length : uint256, var_1250_offset : uint256, var_1250_length : uint256, param_state_memory : mem): (uint256 * mem) = {
    var var, param_state_memory, zero_bool, tmp434, tmp435, tmp436, tmp437, tmp438, tmp439, tmp440, _1, _2, _3;
      {
      zero_bool <- zero_value_for_split_bool;
      var <- zero_bool;
      tmp434,param_state_memory <@ fun_loadVerificationKey(param_state_memory);
      tmp435,param_state_memory <@ usr$loadProof(param_state_memory);
      tmp436,param_state_memory <@ usr$initializeTranscript(param_state_memory);
      tmp437,param_state_memory <@ usr$verifyQuotientEvaluation(param_state_memory);
      tmp438,param_state_memory <@ usr$prepareQueries(param_state_memory);
      tmp439,param_state_memory <@ usr$prepareAggregatedCommitment(param_state_memory);
      tmp440,param_state_memory <@ usr$finalPairing(param_state_memory);
      _1 <- true;
      _2 <- 0;
      param_state_memory <@ MStore(_2, _1, param_state_memory);
      _3 <- 32;
      return (_2, _3);
      return (var, param_state_memory);
      
      }
    }
  
  proc abi_decode_array_uint256_dyn_calldatat_array_uint256_dyn_calldatat_array_uint256_dyn_calldata(headStart : uint256, dataEnd : uint256): (uint256 * uint256 * uint256 * uint256 * uint256 * uint256) = {
    var value0, value1, value2, value3, value4, value5, _1, _2, _3, tmp21, _4, _5, offset, tmp22, _6, _7, tmp23, _8, tmp24, _9, _10, offset_1, tmp25, _11, tmp26, _12, tmp27, _13, _14, offset_2, tmp28, _15, tmp29, _16, tmp30;
      {
      _1 <- 96;
      _2 <- dataEnd - headStart;
      _3 <- slt(_2, _1);
      if (_3)
        {
        tmp21 <@ revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b();
        
        }
      ;
      _4 <- 0;
      _5 <- headStart + _4;
      tmp22 <@ CallDataLoad(_5);
      offset <- tmp22;
      _6 <- 18446744073709551615;
      _7 <- gt(offset, _6);
      if (_7)
        {
        tmp23 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
        
        }
      ;
      _8 <- headStart + offset;
      tmp24 <@ abi_decode_array_uint256_dyn_calldata(_8, dataEnd);
      value0value1, <- tmp24;
      _9 <- 32;
      _10 <- headStart + _9;
      tmp25 <@ CallDataLoad(_10);
      offset_1 <- tmp25;
      _11 <- gt(offset_1, _6);
      if (_11)
        {
        tmp26 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
        
        }
      ;
      _12 <- headStart + offset_1;
      tmp27 <@ abi_decode_array_uint256_dyn_calldata(_12, dataEnd);
      value2value3, <- tmp27;
      _13 <- 64;
      _14 <- headStart + _13;
      tmp28 <@ CallDataLoad(_14);
      offset_2 <- tmp28;
      _15 <- gt(offset_2, _6);
      if (_15)
        {
        tmp29 <@ revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db();
        
        }
      ;
      _16 <- headStart + offset_2;
      tmp30 <@ abi_decode_array_uint256_dyn_calldata(_16, dataEnd);
      value4value5, <- tmp30;
      return (value0, value1, value2, value3, value4, value5);
      
      }
    }
  
  proc usr$getTranscriptChallenge(usr$numberOfChallenge : uint256, param_state_memory : mem): (uint256 * mem) = {
    var usr$challenge, param_state_memory, _1, _2, _3, _4, _5, _6, _7, _8, _9, tmp94;
      {
      _1 <- 2;
      _2 <- 3395;
      param_state_memory <@ MStore8(_2, _1, param_state_memory);
      _3 <- 224;
      _4 <- _3 << usr$numberOfChallenge;
      _5 <- 3460;
      param_state_memory <@ MStore(_5, _4, param_state_memory);
      _6 <- 253 << 1 - 1;
      _7 <- 72;
      _8 <- 3392;
      tmp94 <@ Keccak256(_8, _7);
      _9 <- tmp94;
      usr$challenge <- _9 /\ _6;
      return (usr$challenge, param_state_memory);
      
      }
    }
  
  proc abi_encode_bytes32(headStart : uint256, value0 : uint256, param_state_memory : mem): (uint256 * mem) = {
    var tail, param_state_memory, _1, _2, _3, tmp39;
      {
      _1 <- 32;
      tail <- headStart + _1;
      _2 <- 0;
      _3 <- headStart + _2;
      tmp39,param_state_memory <@ abi_encode_bytes32_to_bytes32(value0, _3, param_state_memory);
      return (tail, param_state_memory);
      
      }
    }
  
  proc usr$modexp(usr$value : uint256, usr$power : uint256, param_state_memory : mem): (uint256 * mem) = {
    var usr$res, param_state_memory, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, tmp49, _11, tmp50, _12, _13, _14, tmp51, tmp52;
      {
      _1 <- 32;
      _2 <- 0;
      param_state_memory <@ MStore(_2, _1, param_state_memory);
      param_state_memory <@ MStore(_1, _1, param_state_memory);
      _3 <- 64;
      param_state_memory <@ MStore(_3, _1, param_state_memory);
      _4 <- 96;
      param_state_memory <@ MStore(_4, usr$value, param_state_memory);
      _5 <- 128;
      param_state_memory <@ MStore(_5, usr$power, param_state_memory);
      _6 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _7 <- 160;
      param_state_memory <@ MStore(_7, _6, param_state_memory);
      _8 <- 192;
      _9 <- 5;
      tmp49 <@ Gas();
      _10 <- tmp49;
      tmp50 <@ StaticCall(_10, _9, _2, _8, _2, _1);
      _11 <- tmp50;
      _12 <- iszero(_11);
      if (_12)
        {
        _13 <- "modexp precompile failed";
        _14 <- 24;
        tmp51,param_state_memory <@ usr$revertWithMessage(_14, _13, param_state_memory);
        
        }
      ;
      tmp52 <@ MLoad(_2, param_state_memory);
      usr$res <- tmp52;
      return (usr$res, param_state_memory);
      
      }
    }
  
  proc usr$finalPairing(param_state_memory : mem): mem = {
    var param_state_memory, _1, usr$u, tmp412, _2, usr$z, tmp413, _3, _4, _5, tmp414, usr$zOmega, _6, _7, tmp415, _8, tmp416, _9, _10, tmp417, _11, tmp418, _12, _13, _14, tmp419, _15, tmp420, tmp421, _16, _17, tmp422, usr$uu, _18, tmp423, _19, tmp424, _20, tmp425, _21, _22, _23, tmp426, _24, _25, _26, _27, _28, _29, _30, _31, _32, _33, tmp427, _34, _35, tmp428, _36, _37, _38, _39, _40, _41, _42, _43, _44, _45, _46, _47, tmp429, usr$success, tmp430, _48, _49, tmp431, _50, tmp432, _51, _52, _53, tmp433;
      {
      _1 <- 4032;
      tmp412 <@ MLoad(_1, param_state_memory);
      usr$u <- tmp412;
      _2 <- 4064;
      tmp413 <@ MLoad(_2, param_state_memory);
      usr$z <- tmp413;
      _3 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _4 <- 13446667982376394161563610564587413125564757801019538732601045199901075958935;
      tmp414 <@ MLoad(_2, param_state_memory);
      _5 <- tmp414;
      usr$zOmega <- mulmod(_5, _4, _3);
      _6 <- 4672;
      _7 <- 4736;
      tmp415,param_state_memory <@ usr$pointSubAssign(_7, _6, param_state_memory);
      _8 <- 3136;
      tmp416,param_state_memory <@ usr$pointMulAndAddIntoDest(_8, usr$z, _7, param_state_memory);
      _9 <- mulmod(usr$zOmega, usr$u, _3);
      _10 <- 3200;
      tmp417,param_state_memory <@ usr$pointMulAndAddIntoDest(_10, _9, _7, param_state_memory);
      tmp418 <@ MLoad(_8, param_state_memory);
      _11 <- tmp418;
      _12 <- 4864;
      param_state_memory <@ MStore(_12, _11, param_state_memory);
      _13 <- 3168;
      tmp419 <@ MLoad(_13, param_state_memory);
      _14 <- tmp419;
      _15 <- 4896;
      param_state_memory <@ MStore(_15, _14, param_state_memory);
      tmp420,param_state_memory <@ usr$pointMulAndAddIntoDest(_10, usr$u, _12, param_state_memory);
      tmp421,param_state_memory <@ usr$pointNegate(_12, param_state_memory);
      _16 <- 1792;
      tmp422 <@ MLoad(_16, param_state_memory);
      _17 <- tmp422;
      if (_17)
        {
        usr$uu <- mulmod(usr$u, usr$u, _3);
        _18 <- 3264;
        tmp423,param_state_memory <@ usr$pointMulAndAddIntoDest(_18, usr$uu, _7, param_state_memory);
        _19 <- 3328;
        tmp424,param_state_memory <@ usr$pointMulAndAddIntoDest(_19, usr$uu, _12, param_state_memory);
        
        }
      ;
      tmp425 <@ MLoad(_7, param_state_memory);
      _20 <- tmp425;
      _21 <- 0;
      param_state_memory <@ MStore(_21, _20, param_state_memory);
      _22 <- 4768;
      tmp426 <@ MLoad(_22, param_state_memory);
      _23 <- tmp426;
      _24 <- 32;
      param_state_memory <@ MStore(_24, _23, param_state_memory);
      _25 <- 11559732032986387107991004021392285783925812861821192530917403151452391805634;
      _26 <- 64;
      param_state_memory <@ MStore(_26, _25, param_state_memory);
      _27 <- 10857046999023057135944570762232829481370756359578518086990519993285655852781;
      _28 <- 96;
      param_state_memory <@ MStore(_28, _27, param_state_memory);
      _29 <- 4082367875863433681332203403145435568316851327593401208105741076214120093531;
      _30 <- 128;
      param_state_memory <@ MStore(_30, _29, param_state_memory);
      _31 <- 8495653923123431417604973247489272438418190587263600148770280649306958101930;
      _32 <- 160;
      param_state_memory <@ MStore(_32, _31, param_state_memory);
      tmp427 <@ MLoad(_12, param_state_memory);
      _33 <- tmp427;
      _34 <- 192;
      param_state_memory <@ MStore(_34, _33, param_state_memory);
      tmp428 <@ MLoad(_15, param_state_memory);
      _35 <- tmp428;
      _36 <- 224;
      param_state_memory <@ MStore(_36, _35, param_state_memory);
      _37 <- 17212635814319756364507010169094758005397460366678210664966334781961899574209;
      _38 <- 256;
      param_state_memory <@ MStore(_38, _37, param_state_memory);
      _39 <- 496075682290949347282619629729389528669750910289829251317610107342504362928;
      _40 <- 288;
      param_state_memory <@ MStore(_40, _39, param_state_memory);
      _41 <- 2255182984359105691812395885056400739448730162863181907784180250290003009508;
      _42 <- 320;
      param_state_memory <@ MStore(_42, _41, param_state_memory);
      _43 <- 15828724851114720558251891430452666121603726704878231219287131634746610441813;
      _44 <- 352;
      param_state_memory <@ MStore(_44, _43, param_state_memory);
      _45 <- 384;
      _46 <- 8;
      tmp429 <@ Gas();
      _47 <- tmp429;
      tmp430 <@ StaticCall(_47, _46, _21, _45, _21, _24);
      usr$success <- tmp430;
      _48 <- iszero(usr$success);
      if (_48)
        {
        _49 <- "finalPairing: precompile failure";
        tmp431,param_state_memory <@ usr$revertWithMessage(_24, _49, param_state_memory);
        
        }
      ;
      tmp432 <@ MLoad(_21, param_state_memory);
      _50 <- tmp432;
      _51 <- iszero(_50);
      if (_51)
        {
        _52 <- "finalPairing: pairing failure";
        _53 <- 29;
        tmp433,param_state_memory <@ usr$revertWithMessage(_53, _52, param_state_memory);
        
        }
      ;
      return param_state_memory;
      
      }
    }
  
  proc revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc usr$updateAggregationChallenge_105(usr$queriesCommitmentPoint : uint256, usr$valueAtZ_Omega : uint256, usr$previousCoeff : uint256, usr$curAggregationChallenge : uint256, usr$curAggregatedOpeningAtZ_Omega : uint256, param_state_memory : mem): (uint256 * uint256 * mem) = {
    var usr$newAggregationChallenge, usr$newAggregatedOpeningAtZ_Omega, param_state_memory, _1, _2, _3, tmp373, _4, _5, tmp374, _6, usr$finalCoeff, _7, tmp375, _8, tmp376, _9;
      {
      _1 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _2 <- 4000;
      tmp373 <@ MLoad(_2, param_state_memory);
      _3 <- tmp373;
      usr$newAggregationChallenge <- mulmod(usr$curAggregationChallenge, _3, _1);
      _4 <- 4032;
      tmp374 <@ MLoad(_4, param_state_memory);
      _5 <- tmp374;
      _6 <- mulmod(usr$newAggregationChallenge, _5, _1);
      usr$finalCoeff <- addmod(usr$previousCoeff, _6, _1);
      _7 <- 4544;
      tmp375,param_state_memory <@ usr$pointMulAndAddIntoDest(usr$queriesCommitmentPoint, usr$finalCoeff, _7, param_state_memory);
      tmp376 <@ MLoad(usr$valueAtZ_Omega, param_state_memory);
      _8 <- tmp376;
      _9 <- mulmod(usr$newAggregationChallenge, _8, _1);
      usr$newAggregatedOpeningAtZ_Omega <- addmod(usr$curAggregatedOpeningAtZ_Omega, _9, _1);
      return (usr$newAggregationChallenge, usr$newAggregatedOpeningAtZ_Omega, param_state_memory);
      
      }
    }
  
  proc external_fun_verify(param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp33, tmp34, _2, tmp35, _3, param, param_1, param_2, param_3, param_4, param_5, tmp36, tmp37;
      {
      tmp33 <@ CallValue();
      _1 <- tmp33;
      if (_1)
        {
        tmp34 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb();
        
        }
      ;
      tmp35 <@ CallDataSize();
      _2 <- tmp35;
      _3 <- 4;
      tmp36 <@ abi_decode_array_uint256_dyn_calldatat_array_uint256_dyn_calldatat_array_uint256_dyn_calldata(_3, _2);
      paramparam_1,param_2,param_3,param_4,param_5, <- tmp36;
      tmp37,param_state_memory <@ fun_verify(param, param_1, param_2, param_3, param_4, param_5, param_state_memory);
       <@ Pop(tmp37);
      return param_state_memory;
      
      }
    }
  
  proc BODY(): unit = {
      {
      tmp0 <@ MemoryGuard(128);
      _1 <- tmp0;
      _2 <- 64;
       <@ MStore(_2, _1);
      tmp1 <@ CallValue();
      _3 <- tmp1;
      if (_3)
        {
        tmp2 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb();
        
        }
      ;
      tmp3 <@ constructor_Verifier();
      tmp4 <@ allocate_unbounded();
      _4 <- tmp4;
      tmp5 <@ DataSize("Verifier_1261_deployed");
      _5 <- tmp5;
      tmp6 <@ DataOffset("Verifier_1261_deployed");
      _6 <- tmp6;
       <@ CodeCopy(_4, _6, _5);
      _7 <- _5;
      return (_4, _5);
      
      }
    }
  
  proc revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc abi_decode_array_uint256_dyn_calldata(offset : uint256, end : uint256): (uint256 * uint256) = {
    var arrayPos, length, _1, _2, _3, _4, tmp17, tmp18, _5, _6, tmp19, _7, _8, _9, _10, tmp20;
      {
      _1 <- 31;
      _2 <- offset + _1;
      _3 <- slt(_2, end);
      _4 <- iszero(_3);
      if (_4)
        {
        tmp17 <@ revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d();
        
        }
      ;
      tmp18 <@ CallDataLoad(offset);
      length <- tmp18;
      _5 <- 18446744073709551615;
      _6 <- gt(length, _5);
      if (_6)
        {
        tmp19 <@ revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490();
        
        }
      ;
      _7 <- 32;
      arrayPos <- offset + _7;
      _8 <- length * _7;
      _9 <- arrayPos + _8;
      _10 <- gt(_9, end);
      if (_10)
        {
        tmp20 <@ revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef();
        
        }
      ;
      return (arrayPos, length);
      
      }
    }
  
  proc external_fun_verificationKeyHash(param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp40, tmp41, _2, tmp42, _3, tmp43, ret, tmp44, memPos, tmp45, memEnd, tmp46, _4;
      {
      tmp40 <@ CallValue();
      _1 <- tmp40;
      if (_1)
        {
        tmp41 <@ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb();
        
        }
      ;
      tmp42 <@ CallDataSize();
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
    }
  
  proc usr$mainGateLinearisationContributionWithV(usr$dest : uint256, usr$stateOpening0AtZ : uint256, usr$stateOpening1AtZ : uint256, usr$stateOpening2AtZ : uint256, usr$stateOpening3AtZ : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp295, _2, tmp296, _3, tmp297, _4, tmp298, _5, _6, _7, tmp299, _8, _9, tmp300, _10, tmp301, _11, _12, tmp302, _13, tmp303, _14, _15, tmp304, _16, _17, tmp305, usr$coeff, tmp306;
      {
      _1 <- 512;
      tmp295,param_state_memory <@ usr$pointMulIntoDest(_1, usr$stateOpening0AtZ, usr$dest, param_state_memory);
      _2 <- 576;
      tmp296,param_state_memory <@ usr$pointMulAndAddIntoDest(_2, usr$stateOpening1AtZ, usr$dest, param_state_memory);
      _3 <- 640;
      tmp297,param_state_memory <@ usr$pointMulAndAddIntoDest(_3, usr$stateOpening2AtZ, usr$dest, param_state_memory);
      _4 <- 704;
      tmp298,param_state_memory <@ usr$pointMulAndAddIntoDest(_4, usr$stateOpening3AtZ, usr$dest, param_state_memory);
      _5 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _6 <- mulmod(usr$stateOpening0AtZ, usr$stateOpening1AtZ, _5);
      _7 <- 768;
      tmp299,param_state_memory <@ usr$pointMulAndAddIntoDest(_7, _6, usr$dest, param_state_memory);
      _8 <- mulmod(usr$stateOpening0AtZ, usr$stateOpening2AtZ, _5);
      _9 <- 832;
      tmp300,param_state_memory <@ usr$pointMulAndAddIntoDest(_9, _8, usr$dest, param_state_memory);
      _10 <- 896;
      tmp301,param_state_memory <@ usr$pointAddAssign(usr$dest, _10, param_state_memory);
      _11 <- 2688;
      tmp302 <@ MLoad(_11, param_state_memory);
      _12 <- tmp302;
      _13 <- 960;
      tmp303,param_state_memory <@ usr$pointMulAndAddIntoDest(_13, _12, usr$dest, param_state_memory);
      _14 <- 4000;
      tmp304 <@ MLoad(_14, param_state_memory);
      _15 <- tmp304;
      _16 <- 2720;
      tmp305 <@ MLoad(_16, param_state_memory);
      _17 <- tmp305;
      usr$coeff <- mulmod(_17, _15, _5);
      tmp306,param_state_memory <@ usr$pointMulIntoDest(usr$dest, usr$coeff, usr$dest, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  proc usr$pointMulIntoDest(usr$point : uint256, usr$s : uint256, usr$dest : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp53, _2, _3, _4, _5, tmp54, _6, _7, _8, _9, tmp55, _10, tmp56, _11, _12, _13, tmp57;
      {
      tmp53 <@ MLoad(usr$point, param_state_memory);
      _1 <- tmp53;
      _2 <- 0;
      param_state_memory <@ MStore(_2, _1, param_state_memory);
      _3 <- 32;
      _4 <- usr$point + _3;
      tmp54 <@ MLoad(_4, param_state_memory);
      _5 <- tmp54;
      param_state_memory <@ MStore(_3, _5, param_state_memory);
      _6 <- 64;
      param_state_memory <@ MStore(_6, usr$s, param_state_memory);
      _7 <- 96;
      _8 <- 7;
      tmp55 <@ Gas();
      _9 <- tmp55;
      tmp56 <@ StaticCall(_9, _8, _2, _7, usr$dest, _6);
      _10 <- tmp56;
      _11 <- iszero(_10);
      if (_11)
        {
        _12 <- "pointMulIntoDest: ecMul failed";
        _13 <- 30;
        tmp57,param_state_memory <@ usr$revertWithMessage(_13, _12, param_state_memory);
        
        }
      ;
      return param_state_memory;
      
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
  
  proc usr$addAssignPermutationLinearisationContributionWithV(usr$dest : uint256, usr$stateOpening0AtZ : uint256, usr$stateOpening1AtZ : uint256, usr$stateOpening2AtZ : uint256, usr$stateOpening3AtZ : uint256, param_state_memory : mem): mem = {
    var param_state_memory, usr$factor, tmp312, _1, tmp313, _2, _3, tmp314, usr$gamma, tmp315, _4, usr$intermediateValue, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, usr$l0AtZ, tmp316, _15, _16, tmp317, _17, _18, tmp318, _19, _20, tmp319, _21, tmp320, _22, _23, tmp321, usr$beta, tmp322, usr$gamma_1, tmp323, _24, _25, tmp324, _26, _27, usr$intermediateValue_1, _28, _29, tmp325, _30, _31, _32, _33, tmp326, _34, _35, _36, tmp327, _37, _38, tmp328, tmp329;
      {
      tmp312 <@ MLoad(3680, param_state_memory);
      usr$factor <- tmp312;
      tmp313 <@ MLoad(3552, param_state_memory);
      _1 <- tmp313;
      _2 <- 4064;
      tmp314 <@ MLoad(_2, param_state_memory);
      _3 <- tmp314;
      tmp315 <@ MLoad(3584, param_state_memory);
      usr$gamma <- tmp315;
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
      tmp316 <@ MLoad(_14, param_state_memory);
      usr$l0AtZ <- tmp316;
      _15 <- 3712;
      tmp317 <@ MLoad(_15, param_state_memory);
      _16 <- tmp317;
      _17 <- mulmod(usr$l0AtZ, _16, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- addmod(usr$factor, _17, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      tmp318 <@ MLoad(4000, param_state_memory);
      _18 <- tmp318;
      usr$factor <- mulmod(usr$factor, _18, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _19 <- 4928;
      param_state_memory <@ MStore(_19, usr$factor, param_state_memory);
      tmp319 <@ MLoad(3552, param_state_memory);
      _20 <- tmp319;
      tmp320 <@ MLoad(3680, param_state_memory);
      _21 <- tmp320;
      usr$factor <- mulmod(_21, _20, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _22 <- 2848;
      tmp321 <@ MLoad(_22, param_state_memory);
      _23 <- tmp321;
      usr$factor <- mulmod(usr$factor, _23, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      tmp322 <@ MLoad(3552, param_state_memory);
      usr$beta <- tmp322;
      tmp323 <@ MLoad(3584, param_state_memory);
      usr$gamma_1 <- tmp323;
      _24 <- 2752;
      tmp324 <@ MLoad(_24, param_state_memory);
      _25 <- tmp324;
      _26 <- mulmod(_25, usr$beta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _27 <- addmod(_26, usr$gamma_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$intermediateValue_1 <- addmod(_27, usr$stateOpening0AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$intermediateValue_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _28 <- 2784;
      tmp325 <@ MLoad(_28, param_state_memory);
      _29 <- tmp325;
      _30 <- mulmod(_29, usr$beta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _31 <- addmod(_30, usr$gamma_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$intermediateValue_1 <- addmod(_31, usr$stateOpening1AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$intermediateValue_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _32 <- 2816;
      tmp326 <@ MLoad(_32, param_state_memory);
      _33 <- tmp326;
      _34 <- mulmod(_33, usr$beta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _35 <- addmod(_34, usr$gamma_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$intermediateValue_1 <- addmod(_35, usr$stateOpening2AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$intermediateValue_1, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      tmp327 <@ MLoad(4000, param_state_memory);
      _36 <- tmp327;
      usr$factor <- mulmod(usr$factor, _36, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _37 <- 4224;
      _38 <- 1344;
      tmp328,param_state_memory <@ usr$pointMulIntoDest(_38, usr$factor, _37, param_state_memory);
      tmp329,param_state_memory <@ usr$pointSubAssign(usr$dest, _37, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  proc usr$verifyQuotientEvaluation(param_state_memory : mem): mem = {
    var param_state_memory, _1, usr$alpha, tmp253, _2, usr$currentAlpha, _3, _4, _5, _6, _7, _8, _9, _10, usr$stateZ, tmp254, _11, _12, tmp255, _13, _14, _15, _16, _17, tmp256, _18, _19, _20, tmp257, _21, tmp258, usr$stateT, _22, _23, tmp259, usr$result, _24, tmp260, _25, tmp261, _26, _27, tmp262, _28, _29, _30, tmp263, usr$vanishing, _31, _32, tmp264, usr$lhs, _33, _34, _35, _36, tmp265;
      {
      _1 <- 3520;
      tmp253 <@ MLoad(_1, param_state_memory);
      usr$alpha <- tmp253;
      _2 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      usr$currentAlpha <- mulmod(usr$alpha, usr$alpha, _2);
      _3 <- 3616;
      param_state_memory <@ MStore(_3, usr$currentAlpha, param_state_memory);
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _4 <- 3648;
      param_state_memory <@ MStore(_4, usr$currentAlpha, param_state_memory);
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _5 <- 3680;
      param_state_memory <@ MStore(_5, usr$currentAlpha, param_state_memory);
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _6 <- 3712;
      param_state_memory <@ MStore(_6, usr$currentAlpha, param_state_memory);
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _7 <- 3744;
      param_state_memory <@ MStore(_7, usr$currentAlpha, param_state_memory);
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _8 <- 3776;
      param_state_memory <@ MStore(_8, usr$currentAlpha, param_state_memory);
      usr$currentAlpha <- mulmod(usr$currentAlpha, usr$alpha, _2);
      _9 <- 3808;
      param_state_memory <@ MStore(_9, usr$currentAlpha, param_state_memory);
      _10 <- 4064;
      tmp254 <@ MLoad(_10, param_state_memory);
      usr$stateZ <- tmp254;
      _11 <- 0;
      tmp255,param_state_memory <@ usr$evaluateLagrangePolyOutOfDomain(_11, usr$stateZ, param_state_memory);
      _12 <- tmp255;
      _13 <- 4128;
      param_state_memory <@ MStore(_13, _12, param_state_memory);
      _14 <- 1;
      _15 <- 67108864;
      _16 <- _15 - _14;
      tmp256,param_state_memory <@ usr$evaluateLagrangePolyOutOfDomain(_16, usr$stateZ, param_state_memory);
      _17 <- tmp256;
      _18 <- 4160;
      param_state_memory <@ MStore(_18, _17, param_state_memory);
      _19 <- 1824;
      tmp257 <@ MLoad(_19, param_state_memory);
      _20 <- tmp257;
      tmp258 <@ MLoad(_13, param_state_memory);
      _21 <- tmp258;
      usr$stateT <- mulmod(_21, _20, _2);
      _22 <- 2720;
      tmp259 <@ MLoad(_22, param_state_memory);
      _23 <- tmp259;
      usr$result <- mulmod(usr$stateT, _23, _2);
      tmp260 <@ usr$permutationQuotientContribution(param_state_memory);
      _24 <- tmp260;
      usr$result <- addmod(usr$result, _24, _2);
      tmp261,param_state_memory <@ usr$lookupQuotientContribution(param_state_memory);
      _25 <- tmp261;
      usr$result <- addmod(usr$result, _25, _2);
      _26 <- 3104;
      tmp262 <@ MLoad(_26, param_state_memory);
      _27 <- tmp262;
      usr$result <- addmod(_27, usr$result, _2);
      _28 <- _2 - _14;
      _29 <- 4192;
      tmp263 <@ MLoad(_29, param_state_memory);
      _30 <- tmp263;
      usr$vanishing <- addmod(_30, _28, _2);
      _31 <- 3072;
      tmp264 <@ MLoad(_31, param_state_memory);
      _32 <- tmp264;
      usr$lhs <- mulmod(_32, usr$vanishing, _2);
      _33 <- usr$lhs = usr$result;
      _34 <- iszero(_33);
      if (_34)
        {
        _35 <- "invalid quotient evaluation";
        _36 <- 27;
        tmp265,param_state_memory <@ usr$revertWithMessage(_36, _35, param_state_memory);
        
        }
      ;
      return param_state_memory;
      
      }
    }
  
  proc revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc usr$updateTranscript(usr$value : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, _2, _3, _4, _5, usr$newState0, tmp92, _6, usr$newState1, tmp93, _7, _8;
      {
      _1 <- 0;
      _2 <- 3395;
      param_state_memory <@ MStore8(_2, _1, param_state_memory);
      _3 <- 3460;
      param_state_memory <@ MStore(_3, usr$value, param_state_memory);
      _4 <- 100;
      _5 <- 3392;
      tmp92 <@ Keccak256(_5, _4);
      usr$newState0 <- tmp92;
      _6 <- 1;
      param_state_memory <@ MStore8(_2, _6, param_state_memory);
      tmp93 <@ Keccak256(_5, _4);
      usr$newState1 <- tmp93;
      _7 <- 3428;
      param_state_memory <@ MStore(_7, usr$newState1, param_state_memory);
      _8 <- 3396;
      param_state_memory <@ MStore(_8, usr$newState0, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  proc usr$pointSubAssign(usr$p1 : uint256, usr$p2 : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp65, _2, _3, _4, _5, tmp66, _6, tmp67, _7, _8, _9, tmp68, _10, _11, _12, _13, _14, _15, tmp69, _16, tmp70, _17, _18, _19, tmp71;
      {
      tmp65 <@ MLoad(usr$p1, param_state_memory);
      _1 <- tmp65;
      _2 <- 0;
      param_state_memory <@ MStore(_2, _1, param_state_memory);
      _3 <- 32;
      _4 <- usr$p1 + _3;
      tmp66 <@ MLoad(_4, param_state_memory);
      _5 <- tmp66;
      param_state_memory <@ MStore(_3, _5, param_state_memory);
      tmp67 <@ MLoad(usr$p2, param_state_memory);
      _6 <- tmp67;
      _7 <- 64;
      param_state_memory <@ MStore(_7, _6, param_state_memory);
      _8 <- usr$p2 + _3;
      tmp68 <@ MLoad(_8, param_state_memory);
      _9 <- tmp68;
      _10 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
      _11 <- _10 - _9;
      _12 <- 96;
      param_state_memory <@ MStore(_12, _11, param_state_memory);
      _13 <- 128;
      _14 <- 6;
      tmp69 <@ Gas();
      _15 <- tmp69;
      tmp70 <@ StaticCall(_15, _14, _2, _13, usr$p1, _7);
      _16 <- tmp70;
      _17 <- iszero(_16);
      if (_17)
        {
        _18 <- "pointSubAssign: ecAdd failed";
        _19 <- 28;
        tmp71,param_state_memory <@ usr$revertWithMessage(_19, _18, param_state_memory);
        
        }
      ;
      return param_state_memory;
      
      }
    }
  
  proc usr$lookupQuotientContribution(param_state_memory : mem): (uint256 * mem) = {
    var usr$res, param_state_memory, _1, usr$betaLookup, tmp283, _2, usr$gammaLookup, tmp284, _3, _4, usr$betaPlusOne, usr$betaGamma, _5, _6, _7, _8, tmp285, _9, _10, tmp286, _11, _12, tmp287, _13, _14, _15, usr$lastOmega, tmp288, _16, _17, _18, tmp289, usr$zMinusLastOmega, _19, _20, _21, tmp290, _22, _23, tmp291, usr$intermediateValue, _24, _25, usr$lnMinusOneAtZ, tmp292, usr$betaGammaPowered, tmp293, _26, usr$alphaPower8, tmp294, _27, usr$subtrahend, _28;
      {
      _1 <- 3872;
      tmp283 <@ MLoad(_1, param_state_memory);
      usr$betaLookup <- tmp283;
      _2 <- 3904;
      tmp284 <@ MLoad(_2, param_state_memory);
      usr$gammaLookup <- tmp284;
      _3 <- 21888242871839275222246405745257275088548364400416034343698204186575808495617;
      _4 <- 1;
      usr$betaPlusOne <- addmod(usr$betaLookup, _4, _3);
      usr$betaGamma <- mulmod(usr$betaPlusOne, usr$gammaLookup, _3);
      _5 <- 3936;
      param_state_memory <@ MStore(_5, usr$betaPlusOne, param_state_memory);
      _6 <- 3968;
      param_state_memory <@ MStore(_6, usr$betaGamma, param_state_memory);
      _7 <- 2880;
      tmp285 <@ MLoad(_7, param_state_memory);
      _8 <- tmp285;
      usr$res <- mulmod(_8, usr$betaLookup, _3);
      usr$res <- addmod(usr$res, usr$betaGamma, _3);
      _9 <- 2912;
      tmp286 <@ MLoad(_9, param_state_memory);
      _10 <- tmp286;
      usr$res <- mulmod(usr$res, _10, _3);
      _11 <- 3744;
      tmp287 <@ MLoad(_11, param_state_memory);
      _12 <- tmp287;
      usr$res <- mulmod(usr$res, _12, _3);
      _13 <- 67108864;
      _14 <- _13 - _4;
      _15 <- 13446667982376394161563610564587413125564757801019538732601045199901075958935;
      tmp288,param_state_memory <@ usr$modexp(_15, _14, param_state_memory);
      usr$lastOmega <- tmp288;
      _16 <- _3 - usr$lastOmega;
      _17 <- 4064;
      tmp289 <@ MLoad(_17, param_state_memory);
      _18 <- tmp289;
      usr$zMinusLastOmega <- addmod(_18, _16, _3);
      _19 <- 4096;
      param_state_memory <@ MStore(_19, usr$zMinusLastOmega, param_state_memory);
      usr$res <- mulmod(usr$res, usr$zMinusLastOmega, _3);
      _20 <- 3776;
      tmp290 <@ MLoad(_20, param_state_memory);
      _21 <- tmp290;
      _22 <- 4128;
      tmp291 <@ MLoad(_22, param_state_memory);
      _23 <- tmp291;
      usr$intermediateValue <- mulmod(_23, _21, _3);
      _24 <- _3 - usr$intermediateValue;
      usr$res <- addmod(usr$res, _24, _3);
      _25 <- 4160;
      tmp292 <@ MLoad(_25, param_state_memory);
      usr$lnMinusOneAtZ <- tmp292;
      tmp293,param_state_memory <@ usr$modexp(usr$betaGamma, _14, param_state_memory);
      usr$betaGammaPowered <- tmp293;
      _26 <- 3808;
      tmp294 <@ MLoad(_26, param_state_memory);
      usr$alphaPower8 <- tmp294;
      _27 <- mulmod(usr$lnMinusOneAtZ, usr$betaGammaPowered, _3);
      usr$subtrahend <- mulmod(_27, usr$alphaPower8, _3);
      _28 <- _3 - usr$subtrahend;
      usr$res <- addmod(usr$res, _28, _3);
      return (usr$res, param_state_memory);
      
      }
    }
  
  proc revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(): unit = {
    var _1;
      {
      _1 <- 0;
      return ();
      
      }
    }
  
  proc usr$addAssignLookupLinearisationContributionWithV(usr$dest : uint256, usr$stateOpening0AtZ : uint256, usr$stateOpening1AtZ : uint256, usr$stateOpening2AtZ : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, usr$factor, tmp330, _2, tmp331, _3, tmp332, _4, _5, tmp333, _6, _7, tmp334, _8, _9, tmp335, _10, _11, tmp336, _12, _13, tmp337, usr$fReconstructed, _14, usr$eta, tmp338, usr$currentEta, _15, _16, _17, _18, tmp339, _19, _20, _21, tmp340, _22, _23, tmp341, _24, _25, tmp342, _26, tmp343, _27, tmp344, _28, _29, tmp345, _30, _31, tmp346, _32, _33, _34, tmp347, _35, _36, tmp348, _37, _38, tmp349, _39;
      {
      _1 <- 2912;
      tmp330 <@ MLoad(_1, param_state_memory);
      usr$factor <- tmp330;
      tmp331 <@ MLoad(3744, param_state_memory);
      _2 <- tmp331;
      usr$factor <- mulmod(usr$factor, _2, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      tmp332 <@ MLoad(4096, param_state_memory);
      _3 <- tmp332;
      usr$factor <- mulmod(usr$factor, _3, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _4 <- 4000;
      tmp333 <@ MLoad(_4, param_state_memory);
      _5 <- tmp333;
      usr$factor <- mulmod(usr$factor, _5, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _6 <- 4992;
      param_state_memory <@ MStore(_6, usr$factor, param_state_memory);
      _7 <- 2976;
      tmp334 <@ MLoad(_7, param_state_memory);
      usr$factor <- tmp334;
      _8 <- 3872;
      tmp335 <@ MLoad(_8, param_state_memory);
      _9 <- tmp335;
      usr$factor <- mulmod(usr$factor, _9, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _10 <- 2944;
      tmp336 <@ MLoad(_10, param_state_memory);
      _11 <- tmp336;
      usr$factor <- addmod(usr$factor, _11, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _12 <- 3968;
      tmp337 <@ MLoad(_12, param_state_memory);
      _13 <- tmp337;
      usr$factor <- addmod(usr$factor, _13, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$fReconstructed <- usr$stateOpening0AtZ;
      _14 <- 3840;
      tmp338 <@ MLoad(_14, param_state_memory);
      usr$eta <- tmp338;
      usr$currentEta <- usr$eta;
      _15 <- mulmod(usr$eta, usr$stateOpening1AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$fReconstructed <- addmod(usr$stateOpening0AtZ, _15, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$currentEta <- mulmod(usr$eta, usr$eta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _16 <- mulmod(usr$currentEta, usr$stateOpening2AtZ, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$fReconstructed <- addmod(usr$fReconstructed, _16, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$currentEta <- mulmod(usr$currentEta, usr$eta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _17 <- 3040;
      tmp339 <@ MLoad(_17, param_state_memory);
      _18 <- tmp339;
      _19 <- mulmod(_18, usr$currentEta, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$fReconstructed <- addmod(usr$fReconstructed, _19, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _20 <- 3008;
      tmp340 <@ MLoad(_20, param_state_memory);
      _21 <- tmp340;
      usr$fReconstructed <- mulmod(usr$fReconstructed, _21, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _22 <- 3904;
      tmp341 <@ MLoad(_22, param_state_memory);
      _23 <- tmp341;
      usr$fReconstructed <- addmod(usr$fReconstructed, _23, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- mulmod(usr$factor, usr$fReconstructed, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _24 <- 3936;
      tmp342 <@ MLoad(_24, param_state_memory);
      _25 <- tmp342;
      usr$factor <- mulmod(usr$factor, _25, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- 21888242871839275222246405745257275088548364400416034343698204186575808495617 - usr$factor;
      tmp343 <@ MLoad(3744, param_state_memory);
      _26 <- tmp343;
      usr$factor <- mulmod(usr$factor, _26, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      tmp344 <@ MLoad(4096, param_state_memory);
      _27 <- tmp344;
      usr$factor <- mulmod(usr$factor, _27, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _28 <- 3776;
      tmp345 <@ MLoad(_28, param_state_memory);
      _29 <- tmp345;
      _30 <- 4128;
      tmp346 <@ MLoad(_30, param_state_memory);
      _31 <- tmp346;
      _32 <- mulmod(_31, _29, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- addmod(usr$factor, _32, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _33 <- 3808;
      tmp347 <@ MLoad(_33, param_state_memory);
      _34 <- tmp347;
      _35 <- 4160;
      tmp348 <@ MLoad(_35, param_state_memory);
      _36 <- tmp348;
      _37 <- mulmod(_36, _34, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      usr$factor <- addmod(usr$factor, _37, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      tmp349 <@ MLoad(_4, param_state_memory);
      _38 <- tmp349;
      usr$factor <- mulmod(usr$factor, _38, 21888242871839275222246405745257275088548364400416034343698204186575808495617);
      _39 <- 4960;
      param_state_memory <@ MStore(_39, usr$factor, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  proc usr$pointAddAssign(usr$p1 : uint256, usr$p2 : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp72, _2, _3, _4, _5, tmp73, _6, tmp74, _7, _8, _9, tmp75, _10, _11, _12, _13, tmp76, _14, tmp77, _15, _16, _17, tmp78;
      {
      tmp72 <@ MLoad(usr$p1, param_state_memory);
      _1 <- tmp72;
      _2 <- 0;
      param_state_memory <@ MStore(_2, _1, param_state_memory);
      _3 <- 32;
      _4 <- usr$p1 + _3;
      tmp73 <@ MLoad(_4, param_state_memory);
      _5 <- tmp73;
      param_state_memory <@ MStore(_3, _5, param_state_memory);
      tmp74 <@ MLoad(usr$p2, param_state_memory);
      _6 <- tmp74;
      _7 <- 64;
      param_state_memory <@ MStore(_7, _6, param_state_memory);
      _8 <- usr$p2 + _3;
      tmp75 <@ MLoad(_8, param_state_memory);
      _9 <- tmp75;
      _10 <- 96;
      param_state_memory <@ MStore(_10, _9, param_state_memory);
      _11 <- 128;
      _12 <- 6;
      tmp76 <@ Gas();
      _13 <- tmp76;
      tmp77 <@ StaticCall(_13, _12, _2, _11, usr$p1, _7);
      _14 <- tmp77;
      _15 <- iszero(_14);
      if (_15)
        {
        _16 <- "pointAddAssign: ecAdd failed";
        _17 <- 28;
        tmp78,param_state_memory <@ usr$revertWithMessage(_17, _16, param_state_memory);
        
        }
      ;
      return param_state_memory;
      
      }
    }
  
  proc usr$pointMulAndAddIntoDest(usr$point : uint256, usr$s : uint256, usr$dest : uint256, param_state_memory : mem): mem = {
    var param_state_memory, _1, tmp79, _2, _3, _4, _5, tmp80, _6, _7, _8, _9, tmp81, usr$success, tmp82, _10, tmp83, _11, _12, tmp84, _13, _14, _15, tmp85, _16, tmp86, _17, _18, _19, tmp87;
      {
      tmp79 <@ MLoad(usr$point, param_state_memory);
      _1 <- tmp79;
      _2 <- 0;
      param_state_memory <@ MStore(_2, _1, param_state_memory);
      _3 <- 32;
      _4 <- usr$point + _3;
      tmp80 <@ MLoad(_4, param_state_memory);
      _5 <- tmp80;
      param_state_memory <@ MStore(_3, _5, param_state_memory);
      _6 <- 64;
      param_state_memory <@ MStore(_6, usr$s, param_state_memory);
      _7 <- 96;
      _8 <- 7;
      tmp81 <@ Gas();
      _9 <- tmp81;
      tmp82 <@ StaticCall(_9, _8, _2, _7, _2, _6);
      usr$success <- tmp82;
      tmp83 <@ MLoad(usr$dest, param_state_memory);
      _10 <- tmp83;
      param_state_memory <@ MStore(_6, _10, param_state_memory);
      _11 <- usr$dest + _3;
      tmp84 <@ MLoad(_11, param_state_memory);
      _12 <- tmp84;
      param_state_memory <@ MStore(_7, _12, param_state_memory);
      _13 <- 128;
      _14 <- 6;
      tmp85 <@ Gas();
      _15 <- tmp85;
      tmp86 <@ StaticCall(_15, _14, _2, _13, usr$dest, _6);
      _16 <- tmp86;
      usr$success <- usr$success /\ _16;
      _17 <- iszero(usr$success);
      if (_17)
        {
        _18 <- "pointMulAndAddIntoDest";
        _19 <- 22;
        tmp87,param_state_memory <@ usr$revertWithMessage(_19, _18, param_state_memory);
        
        }
      ;
      return param_state_memory;
      
      }
    }
  
  proc fun_loadVerificationKey(param_state_memory : mem): mem = {
    var param_state_memory, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21, _22, _23, _24, _25, _26, _27, _28, _29, _30, _31, _32, _33, _34, _35, _36, _37, _38, _39, _40, _41, _42, _43, _44, _45, _46, _47, _48, _49, _50, _51, _52, _53, _54, _55, _56, _57, _58, _59, _60, _61, _62, _63, _64, _65, _66, _67, _68, _69, _70, _71, _72, _73, _74, _75, _76, _77, _78, _79, _80, _81, _82;
      {
      _1 <- 8752182643819278825281358491109311747488397345835400146720638359015287854690;
      _2 <- 512;
      param_state_memory <@ MStore(_2, _1, param_state_memory);
      _3 <- 11702890106774794311109464320829961639285524182517416836480964755620593036625;
      _4 <- 544;
      param_state_memory <@ MStore(_4, _3, param_state_memory);
      _5 <- 20333726085237242816528533108173405517277666887513325731527458638169740323846;
      _6 <- 576;
      param_state_memory <@ MStore(_6, _5, param_state_memory);
      _7 <- 20895759739260899082484353863151962651671811489085862903974918191239970565727;
      _8 <- 608;
      param_state_memory <@ MStore(_8, _7, param_state_memory);
      _9 <- 1568732599965362807326380099663611053862348508639087822144187543479274466412;
      _10 <- 640;
      param_state_memory <@ MStore(_10, _9, param_state_memory);
      _11 <- 5821054758250780059685638301776364871013117602597489359484409980131967326794;
      _12 <- 672;
      param_state_memory <@ MStore(_12, _11, param_state_memory);
      _13 <- 1869564366554527726271945732583360837778279311090061338642468249261166609475;
      _14 <- 704;
      param_state_memory <@ MStore(_14, _13, param_state_memory);
      _15 <- 6787073056745945161826226704190290609825180409911049644428579916838155209697;
      _16 <- 736;
      param_state_memory <@ MStore(_16, _15, param_state_memory);
      _17 <- 457576930265342335264945522969406804501107665328727087867171094316559181535;
      _18 <- 768;
      param_state_memory <@ MStore(_18, _17, param_state_memory);
      _19 <- 15424863073888926344027107060444259361026863904290125685775015743583967752523;
      _20 <- 800;
      param_state_memory <@ MStore(_20, _19, param_state_memory);
      _21 <- 17470132079837949645292768946901897910488674334073656384858846314172720305794;
      _22 <- 832;
      param_state_memory <@ MStore(_22, _21, param_state_memory);
      _23 <- 545412623592733862227844066395948813122937527333953380716629283051527996076;
      _24 <- 864;
      param_state_memory <@ MStore(_24, _23, param_state_memory);
      _25 <- 3542620684081214281078362979824071457719243923292217179618867142734017714197;
      _26 <- 896;
      param_state_memory <@ MStore(_26, _25, param_state_memory);
      _27 <- 10380438707000372753007289103897630883671902212004026295360039945231108187502;
      _28 <- 928;
      param_state_memory <@ MStore(_28, _27, param_state_memory);
      _29 <- 13086775255118926036233880981068687796723800497694631087151014741591951564618;
      _30 <- 960;
      param_state_memory <@ MStore(_30, _29, param_state_memory);
      _31 <- 97194583370920108185062801930585216368005987855712538133473341181290744675;
      _32 <- 992;
      param_state_memory <@ MStore(_32, _31, param_state_memory);
      _33 <- 11090534100914016361232447120294745393211436081860550365760620284449885924457;
      _34 <- 1024;
      param_state_memory <@ MStore(_34, _33, param_state_memory);
      _35 <- 6190121082107679677011313308624936965782748053078710395209485205617091614781;
      _36 <- 1056;
      param_state_memory <@ MStore(_36, _35, param_state_memory);
      _37 <- 15086136319636422536776088427553286399949509263897119922379735045147898875009;
      _38 <- 1088;
      param_state_memory <@ MStore(_38, _37, param_state_memory);
      _39 <- 14330561162787072568797012175184761164763459595199124517037991495673925464785;
      _40 <- 1120;
      param_state_memory <@ MStore(_40, _39, param_state_memory);
      _41 <- 21323538885080684424185174689480993185750201390966223018512354418490677522148;
      _42 <- 1152;
      param_state_memory <@ MStore(_42, _41, param_state_memory);
      _43 <- 13825385863192118646834397710139923872086647553258488355179808994788744210563;
      _44 <- 1184;
      param_state_memory <@ MStore(_44, _43, param_state_memory);
      _45 <- 8390759602848414205412884900126185284679301543388803089358900543850868129488;
      _46 <- 1216;
      param_state_memory <@ MStore(_46, _45, param_state_memory);
      _47 <- 7069161667387011886642940009688789554068768218554020114127791736575843662652;
      _48 <- 1248;
      param_state_memory <@ MStore(_48, _47, param_state_memory);
      _49 <- 21779692208264067614279093821878517213862501879831804234566704419708093761485;
      _50 <- 1280;
      param_state_memory <@ MStore(_50, _49, param_state_memory);
      _51 <- 14513193766097634962386283396255157053671281137962954471134782133605379519908;
      _52 <- 1312;
      param_state_memory <@ MStore(_52, _51, param_state_memory);
      _53 <- 4751267043421347170875860608378639586591867931662910797110300384786346064625;
      _54 <- 1344;
      param_state_memory <@ MStore(_54, _53, param_state_memory);
      _55 <- 11385717438670984215358012358002661303410243223751533068904005282628107986385;
      _56 <- 1376;
      param_state_memory <@ MStore(_56, _55, param_state_memory);
      _57 <- 20045313662746578028950791395157660351198208045597010788369662325700141348443;
      _58 <- 1472;
      param_state_memory <@ MStore(_58, _57, param_state_memory);
      _59 <- 2200761695078532224145807378118591946349840073460005094399078719163643466856;
      _60 <- 1504;
      param_state_memory <@ MStore(_60, _59, param_state_memory);
      _61 <- 13866646217607640441607041956684111087071997201218815349460750486791109380780;
      _62 <- 1536;
      param_state_memory <@ MStore(_62, _61, param_state_memory);
      _63 <- 13178446611795019678701878053235714968797421377761816259103804833273256298333;
      _64 <- 1568;
      param_state_memory <@ MStore(_64, _63, param_state_memory);
      _65 <- 5057503605752869531452842486824745179648819794307492731589448195268672785801;
      _66 <- 1600;
      param_state_memory <@ MStore(_66, _65, param_state_memory);
      _67 <- 8597434312520299647191152876265164941580478223412397470356037586993894367875;
      _68 <- 1632;
      param_state_memory <@ MStore(_68, _67, param_state_memory);
      _69 <- 1342318055425277544055386589364579054544440640110901993487861472578322387903;
      _70 <- 1664;
      param_state_memory <@ MStore(_70, _69, param_state_memory);
      _71 <- 4438354282468267034382897187461199764068502038746983055473062465446039509158;
      _72 <- 1696;
      param_state_memory <@ MStore(_72, _71, param_state_memory);
      _73 <- 21714794642552531775933093644480516421064284615960245486122726724547638127878;
      _74 <- 1408;
      param_state_memory <@ MStore(_74, _73, param_state_memory);
      _75 <- 20374981665942106195451736226451722737514281476778224282304648903722926579601;
      _76 <- 1440;
      param_state_memory <@ MStore(_76, _75, param_state_memory);
      _77 <- 196778531949039689886328474582670216324308721975620885373710029662715787742;
      _78 <- 1728;
      param_state_memory <@ MStore(_78, _77, param_state_memory);
      _79 <- 11005776646725047106517461026899305486268481542412200771754169232553006481646;
      _80 <- 1760;
      param_state_memory <@ MStore(_80, _79, param_state_memory);
      _81 <- 0;
      _82 <- 1792;
      param_state_memory <@ MStore(_82, _81, param_state_memory);
      return param_state_memory;
      
      }
    }
  
  
  }
(* End Verifier_1261 *)
