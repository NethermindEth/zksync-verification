require import FinalPairing.
require import InitializeTranscript.
require import LoadProof.
require import LoadVerificationKey.
require import PrepareAggregatedCommitment.
require import PrepareQueries.
require import UInt256.
require import Verifier.
require import VerifyQuotientEvaluation.
require import YulPrimops.

module Verify = {
  proc low(var__offset : uint256, var_length : uint256, var_offset : uint256, var__length : uint256, var_1250_offset : uint256, var_1250_length : uint256): uint256 = {
    LoadVerificationKey.low();
    LoadProof.low();
    InitializeTranscript.low();
    VerifyQuotientEvaluation.low();
    PrepareQueries.low();
    PrepareAggregatedCommitment.low();
    FinalPairing.low();
    Primops.mstore(W256.zero, W256.one);
    Primops.evm_return(W256.zero, W256.of_int 32);
    return zero_value_for_split_bool;
  }
  
  proc mid() : int = {
    var vkGateSetup0X, vkGateSetup0Y,
        vkGateSetup1X, vkGateSetup1Y,
        vkGateSetup2X, vkGateSetup2Y,
        vkGateSetup3X, vkGateSetup3Y,
        vkGateSetup4X, vkGateSetup4Y,
        vkGateSetup5X, vkGateSetup5Y,
        vkGateSetup6X, vkGateSetup6Y,
        vkGateSetup7X, vkGateSetup7Y : int;
    var vkGateSelector0X, vkGateSelector1X, 
        vkGateSelector0Y, vkGateSelector1Y: int;
    var vkPermutation0X, vkPermutation0Y, 
        vkPermutation1X, vkPermutation1Y, 
        vkPermutation2X, vkPermutation2Y, 
        vkPermutation3X, vkPermutation3Y: int;
    var vkLookupTable0X, vkLookupTable0Y,
        vkLookupTable1X, vkLookupTable1Y,
        vkLookupTable2X, vkLookupTable2Y,
        vkLookupTable3X, vkLookupTable3Y: int;
    var vkLookupSelectorX, vkLookupSelectorY: int;
    var vkLookupTableTypeX, vkLookupTableTypeY: int;
    var vkRecursiveFlag: int;

    vkGateSetup0X <- 8752182643819278825281358491109311747488397345835400146720638359015287854690;
    vkGateSetup0Y <- 11702890106774794311109464320829961639285524182517416836480964755620593036625;
    vkGateSetup1X <- 20333726085237242816528533108173405517277666887513325731527458638169740323846;
    vkGateSetup1Y <- 20895759739260899082484353863151962651671811489085862903974918191239970565727;
    vkGateSetup2X <- 1568732599965362807326380099663611053862348508639087822144187543479274466412;
    vkGateSetup2Y <- 5821054758250780059685638301776364871013117602597489359484409980131967326794;
    vkGateSetup3X <- 1869564366554527726271945732583360837778279311090061338642468249261166609475;
    vkGateSetup3Y <- 6787073056745945161826226704190290609825180409911049644428579916838155209697;
    vkGateSetup4X <- 457576930265342335264945522969406804501107665328727087867171094316559181535;
    vkGateSetup4Y <- 15424863073888926344027107060444259361026863904290125685775015743583967752523;
    vkGateSetup5X <- 17470132079837949645292768946901897910488674334073656384858846314172720305794;
    vkGateSetup5Y <- 545412623592733862227844066395948813122937527333953380716629283051527996076;
    vkGateSetup6X <- 3542620684081214281078362979824071457719243923292217179618867142734017714197;
    vkGateSetup6Y <- 10380438707000372753007289103897630883671902212004026295360039945231108187502;
    vkGateSetup7X <- 13086775255118926036233880981068687796723800497694631087151014741591951564618;
    vkGateSetup7Y <- 97194583370920108185062801930585216368005987855712538133473341181290744675;
    
    vkGateSelector0X <- 11090534100914016361232447120294745393211436081860550365760620284449885924457;
    vkGateSelector0Y <- 6190121082107679677011313308624936965782748053078710395209485205617091614781;
    vkGateSelector1X <- 15086136319636422536776088427553286399949509263897119922379735045147898875009;
    vkGateSelector1Y <- 14330561162787072568797012175184761164763459595199124517037991495673925464785;

    vkPermutation0X <- 21323538885080684424185174689480993185750201390966223018512354418490677522148;
    vkPermutation0Y <- 13825385863192118646834397710139923872086647553258488355179808994788744210563;
    vkPermutation1X <- 8390759602848414205412884900126185284679301543388803089358900543850868129488;
    vkPermutation1Y <- 7069161667387011886642940009688789554068768218554020114127791736575843662652;
    vkPermutation2X <- 21779692208264067614279093821878517213862501879831804234566704419708093761485;
    vkPermutation2Y <- 14513193766097634962386283396255157053671281137962954471134782133605379519908;
    vkPermutation3X <- 4751267043421347170875860608378639586591867931662910797110300384786346064625;
    vkPermutation3Y <- 11385717438670984215358012358002661303410243223751533068904005282628107986385;

    vkLookupTable0X <- 20045313662746578028950791395157660351198208045597010788369662325700141348443;
    vkLookupTable0Y <- 2200761695078532224145807378118591946349840073460005094399078719163643466856;
    vkLookupTable1X <- 13866646217607640441607041956684111087071997201218815349460750486791109380780;
    vkLookupTable1Y <- 13178446611795019678701878053235714968797421377761816259103804833273256298333;
    vkLookupTable2X <- 5057503605752869531452842486824745179648819794307492731589448195268672785801;
    vkLookupTable2Y <- 8597434312520299647191152876265164941580478223412397470356037586993894367875;
    vkLookupTable3X <- 1342318055425277544055386589364579054544440640110901993487861472578322387903;
    vkLookupTable3Y <- 4438354282468267034382897187461199764068502038746983055473062465446039509158;

    vkLookupSelectorX <- 21714794642552531775933093644480516421064284615960245486122726724547638127878;
    vkLookupSelectorY <- 20374981665942106195451736226451722737514281476778224282304648903722926579601;

    vkLookupTableTypeX <- 196778531949039689886328474582670216324308721975620885373710029662715787742;
    vkLookupTableTypeY <- 11005776646725047106517461026899305486268481542412200771754169232553006481646;

    vkRecursiveFlag <- 0;
    
    return 0;
}

}.

lemma verify_extracted_equiv_low:
    equiv [
      Verifier_1261.fun_verify ~ Verify.low:
      ={arg, glob Verify} ==>
      ={res, glob Verify}
    ].
    proof.
      proc.
      inline Primops.evm_return. wp.
      inline Primops.mstore. wp.
      call finalPairing_extracted_equiv_low.
      call prepareAggregatedCommitment_extracted_equiv_low.
      call prepareQueries_extracted_equiv_low.
      call verifyQuotientEvaluation_extracted_equiv_low.
      call initializeTranscript_extracted_equiv_low.
      call loadProof_extracted_equiv_low.
      call loadVerificationKey_extracted_equiv_low.
      wp. skip. by progress.
    qed.

import MemoryMap VerifierConsts ConcretePrimops PurePrimops.

op verify_memory_footprint (m: mem) =
let m1 = loadVerificationKey_memory_footprint m in
m1.

lemma verify_low_equiv_mid (memory : mem):
equiv [
    Verify.low ~ Verify.mid :
      !Primops.reverted{1} /\ 
      Primops.memory{1} = memory
      ==>
      !Primops.reverted{1} /\
      Primops.memory{1} = loadVerificationKey_memory_footprint memory
    ].
proof. proc.
inline LoadVerificationKey.low.
pose m1 := store memory VK_GATE_SETUP_0_X_SLOT (W256.of_int 8752182643819278825281358491109311747488397345835400146720638359015287854690).
pose m2  := store m1 VK_GATE_SETUP_0_Y_SLOT (W256.of_int 11702890106774794311109464320829961639285524182517416836480964755620593036625).
pose m3  := store m2 VK_GATE_SETUP_1_X_SLOT (W256.of_int 20333726085237242816528533108173405517277666887513325731527458638169740323846).
pose m4  := store m3 VK_GATE_SETUP_1_Y_SLOT (W256.of_int 20895759739260899082484353863151962651671811489085862903974918191239970565727).
pose m5  := store m4 VK_GATE_SETUP_2_X_SLOT (W256.of_int 1568732599965362807326380099663611053862348508639087822144187543479274466412).
pose m6  := store m5 VK_GATE_SETUP_2_Y_SLOT (W256.of_int 5821054758250780059685638301776364871013117602597489359484409980131967326794).
pose m7  := store m6 VK_GATE_SETUP_3_X_SLOT (W256.of_int 1869564366554527726271945732583360837778279311090061338642468249261166609475).
pose m8  := store m7 VK_GATE_SETUP_3_Y_SLOT (W256.of_int 6787073056745945161826226704190290609825180409911049644428579916838155209697).
pose m9  := store m8 VK_GATE_SETUP_4_X_SLOT (W256.of_int 457576930265342335264945522969406804501107665328727087867171094316559181535).
pose m10 := store m9 VK_GATE_SETUP_4_Y_SLOT (W256.of_int 15424863073888926344027107060444259361026863904290125685775015743583967752523).
pose m11 := store m10 VK_GATE_SETUP_5_X_SLOT (W256.of_int 17470132079837949645292768946901897910488674334073656384858846314172720305794).
pose m12 := store m11 VK_GATE_SETUP_5_Y_SLOT (W256.of_int 545412623592733862227844066395948813122937527333953380716629283051527996076).
pose m13 := store m12 VK_GATE_SETUP_6_X_SLOT (W256.of_int 3542620684081214281078362979824071457719243923292217179618867142734017714197).
pose m14 := store m13 VK_GATE_SETUP_6_Y_SLOT (W256.of_int 10380438707000372753007289103897630883671902212004026295360039945231108187502).
pose m15 := store m14 VK_GATE_SETUP_7_X_SLOT (W256.of_int 13086775255118926036233880981068687796723800497694631087151014741591951564618).
pose m16 := store m15 VK_GATE_SETUP_7_Y_SLOT (W256.of_int 97194583370920108185062801930585216368005987855712538133473341181290744675).
pose m17 := store m16 VK_GATE_SELECTORS_0_X_SLOT (W256.of_int 11090534100914016361232447120294745393211436081860550365760620284449885924457).
pose m18 := store m17 VK_GATE_SELECTORS_0_Y_SLOT (W256.of_int 6190121082107679677011313308624936965782748053078710395209485205617091614781).
pose m19 := store m18 VK_GATE_SELECTORS_1_X_SLOT (W256.of_int 15086136319636422536776088427553286399949509263897119922379735045147898875009).
pose m20 := store m19 VK_GATE_SELECTORS_1_Y_SLOT (W256.of_int 14330561162787072568797012175184761164763459595199124517037991495673925464785).
pose m21 := store m20 VK_PERMUTATION_0_X_SLOT (W256.of_int 21323538885080684424185174689480993185750201390966223018512354418490677522148).
pose m22 := store m21 VK_PERMUTATION_0_Y_SLOT (W256.of_int 13825385863192118646834397710139923872086647553258488355179808994788744210563).
pose m23 := store m22 VK_PERMUTATION_1_X_SLOT (W256.of_int 8390759602848414205412884900126185284679301543388803089358900543850868129488).
pose m24 := store m23 VK_PERMUTATION_1_Y_SLOT (W256.of_int 7069161667387011886642940009688789554068768218554020114127791736575843662652).
pose m25 := store m24 VK_PERMUTATION_2_X_SLOT (W256.of_int 21779692208264067614279093821878517213862501879831804234566704419708093761485).
pose m26 := store m25 VK_PERMUTATION_2_Y_SLOT (W256.of_int 14513193766097634962386283396255157053671281137962954471134782133605379519908).
pose m27 := store m26 VK_PERMUTATION_3_X_SLOT (W256.of_int 4751267043421347170875860608378639586591867931662910797110300384786346064625).
pose m28 := store m27 VK_PERMUTATION_3_Y_SLOT (W256.of_int 11385717438670984215358012358002661303410243223751533068904005282628107986385).
pose m29 := store m28 VK_LOOKUP_TABLE_0_X_SLOT (W256.of_int 20045313662746578028950791395157660351198208045597010788369662325700141348443).
pose m30 := store m29 VK_LOOKUP_TABLE_0_Y_SLOT (W256.of_int 2200761695078532224145807378118591946349840073460005094399078719163643466856).
pose m31 := store m30 VK_LOOKUP_TABLE_1_X_SLOT (W256.of_int 13866646217607640441607041956684111087071997201218815349460750486791109380780).
pose m32 := store m31 VK_LOOKUP_TABLE_1_Y_SLOT (W256.of_int 13178446611795019678701878053235714968797421377761816259103804833273256298333).
pose m33 := store m32 VK_LOOKUP_TABLE_2_X_SLOT (W256.of_int 5057503605752869531452842486824745179648819794307492731589448195268672785801).
pose m34 := store m33 VK_LOOKUP_TABLE_2_Y_SLOT (W256.of_int 8597434312520299647191152876265164941580478223412397470356037586993894367875).
pose m35 := store m34 VK_LOOKUP_TABLE_3_X_SLOT (W256.of_int 1342318055425277544055386589364579054544440640110901993487861472578322387903).
pose m36 := store m35 VK_LOOKUP_TABLE_3_Y_SLOT (W256.of_int 4438354282468267034382897187461199764068502038746983055473062465446039509158).
pose m37 := store m36 VK_LOOKUP_SELECTOR_X_SLOT (W256.of_int 21714794642552531775933093644480516421064284615960245486122726724547638127878).
pose m38 := store m37 VK_LOOKUP_SELECTOR_Y_SLOT (W256.of_int 20374981665942106195451736226451722737514281476778224282304648903722926579601).
pose m39 := store m38 VK_LOOKUP_TABLE_TYPE_X_SLOT (W256.of_int 196778531949039689886328474582670216324308721975620885373710029662715787742).
pose m40 := store m39 VK_LOOKUP_TABLE_TYPE_Y_SLOT (W256.of_int 11005776646725047106517461026899305486268481542412200771754169232553006481646).
pose m41 := store m40 VK_RECURSIVE_FLAG_SLOT W256.zero.

pose mlvk := loadVerificationKey_memory_footprint memory.

seq 41 41: (
!Primops.reverted{1} /\ 
Primops.memory{1} = mlvk /\
W256.to_uint (load mlvk VK_GATE_SETUP_0_X_SLOT) = vkGateSetup0X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_0_Y_SLOT) = vkGateSetup0Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_1_X_SLOT) = vkGateSetup1X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_1_Y_SLOT) = vkGateSetup1Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_2_X_SLOT) = vkGateSetup2X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_2_Y_SLOT) = vkGateSetup2Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_3_X_SLOT) = vkGateSetup3X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_3_Y_SLOT) = vkGateSetup3Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_4_X_SLOT) = vkGateSetup4X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_4_Y_SLOT) = vkGateSetup4Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_5_X_SLOT) = vkGateSetup5X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_5_Y_SLOT) = vkGateSetup5Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_6_X_SLOT) = vkGateSetup6X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_6_Y_SLOT) = vkGateSetup6Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_7_X_SLOT) = vkGateSetup7X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_7_Y_SLOT) = vkGateSetup7Y{2} /\
W256.to_uint (load mlvk VK_GATE_SELECTORS_0_X_SLOT) = vkGateSelector0X{2} /\ 
W256.to_uint (load mlvk VK_GATE_SELECTORS_0_Y_SLOT) = vkGateSelector0Y{2} /\
W256.to_uint (load mlvk VK_GATE_SELECTORS_1_X_SLOT) = vkGateSelector1X{2} /\
W256.to_uint (load mlvk VK_GATE_SELECTORS_1_Y_SLOT) = vkGateSelector1Y{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_0_X_SLOT) = vkPermutation0X{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_0_Y_SLOT) = vkPermutation0Y{2} /\   
W256.to_uint (load mlvk VK_PERMUTATION_1_X_SLOT) = vkPermutation1X{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_1_Y_SLOT) = vkPermutation1Y{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_2_X_SLOT) = vkPermutation2X{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_2_Y_SLOT) = vkPermutation2Y{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_3_X_SLOT) = vkPermutation3X{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_3_Y_SLOT) = vkPermutation3Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_0_X_SLOT) = vkLookupTable0X{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_0_Y_SLOT) = vkLookupTable0Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_1_X_SLOT) = vkLookupTable1X{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_1_Y_SLOT) = vkLookupTable1Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_2_X_SLOT) = vkLookupTable2X{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_2_Y_SLOT) = vkLookupTable2Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_3_X_SLOT) = vkLookupTable3X{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_3_Y_SLOT) = vkLookupTable3Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_SELECTOR_X_SLOT) = vkLookupSelectorX{2} /\
W256.to_uint (load mlvk VK_LOOKUP_SELECTOR_Y_SLOT) = vkLookupSelectorY{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_TYPE_X_SLOT) = vkLookupTableTypeX{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) = vkLookupTableTypeY{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) = vkLookupTableTypeY{2} /\
W256.to_uint (load mlvk VK_RECURSIVE_FLAG_SLOT) = vkRecursiveFlag{2}).
wp; inline LoadVerificationKey.low.

call{1} (ConcretePrimops.mstore_pspec m40 VK_RECURSIVE_FLAG_SLOT W256.zero);
call{1} (ConcretePrimops.mstore_pspec m39 VK_LOOKUP_TABLE_TYPE_Y_SLOT (W256.of_int 11005776646725047106517461026899305486268481542412200771754169232553006481646));
call{1} (ConcretePrimops.mstore_pspec m38 VK_LOOKUP_TABLE_TYPE_X_SLOT (W256.of_int 196778531949039689886328474582670216324308721975620885373710029662715787742));
call{1} (ConcretePrimops.mstore_pspec m37 VK_LOOKUP_SELECTOR_Y_SLOT (W256.of_int 20374981665942106195451736226451722737514281476778224282304648903722926579601));
call{1} (ConcretePrimops.mstore_pspec m36 VK_LOOKUP_SELECTOR_X_SLOT (W256.of_int 21714794642552531775933093644480516421064284615960245486122726724547638127878));
call{1} (ConcretePrimops.mstore_pspec m35 VK_LOOKUP_TABLE_3_Y_SLOT (W256.of_int 4438354282468267034382897187461199764068502038746983055473062465446039509158));
call{1} (ConcretePrimops.mstore_pspec m34 VK_LOOKUP_TABLE_3_X_SLOT (W256.of_int 1342318055425277544055386589364579054544440640110901993487861472578322387903));
call{1} (ConcretePrimops.mstore_pspec m33 VK_LOOKUP_TABLE_2_Y_SLOT (W256.of_int 8597434312520299647191152876265164941580478223412397470356037586993894367875));
call{1} (ConcretePrimops.mstore_pspec m32 VK_LOOKUP_TABLE_2_X_SLOT (W256.of_int 5057503605752869531452842486824745179648819794307492731589448195268672785801));
call{1} (ConcretePrimops.mstore_pspec m31 VK_LOOKUP_TABLE_1_Y_SLOT (W256.of_int 13178446611795019678701878053235714968797421377761816259103804833273256298333));
call{1} (ConcretePrimops.mstore_pspec m30 VK_LOOKUP_TABLE_1_X_SLOT (W256.of_int 13866646217607640441607041956684111087071997201218815349460750486791109380780));
call{1} (ConcretePrimops.mstore_pspec m29 VK_LOOKUP_TABLE_0_Y_SLOT (W256.of_int 2200761695078532224145807378118591946349840073460005094399078719163643466856));
call{1} (ConcretePrimops.mstore_pspec m28 VK_LOOKUP_TABLE_0_X_SLOT (W256.of_int 20045313662746578028950791395157660351198208045597010788369662325700141348443));
call{1} (ConcretePrimops.mstore_pspec m27 VK_PERMUTATION_3_Y_SLOT (W256.of_int 11385717438670984215358012358002661303410243223751533068904005282628107986385));
call{1} (ConcretePrimops.mstore_pspec m26 VK_PERMUTATION_3_X_SLOT (W256.of_int 4751267043421347170875860608378639586591867931662910797110300384786346064625));
call{1} (ConcretePrimops.mstore_pspec m25 VK_PERMUTATION_2_Y_SLOT (W256.of_int 14513193766097634962386283396255157053671281137962954471134782133605379519908));
call{1} (ConcretePrimops.mstore_pspec m24 VK_PERMUTATION_2_X_SLOT (W256.of_int 21779692208264067614279093821878517213862501879831804234566704419708093761485));
call{1} (ConcretePrimops.mstore_pspec m23 VK_PERMUTATION_1_Y_SLOT (W256.of_int 7069161667387011886642940009688789554068768218554020114127791736575843662652));
call{1} (ConcretePrimops.mstore_pspec m22 VK_PERMUTATION_1_X_SLOT (W256.of_int 8390759602848414205412884900126185284679301543388803089358900543850868129488));
call{1} (ConcretePrimops.mstore_pspec m21 VK_PERMUTATION_0_Y_SLOT (W256.of_int 13825385863192118646834397710139923872086647553258488355179808994788744210563));
call{1} (ConcretePrimops.mstore_pspec m20 VK_PERMUTATION_0_X_SLOT (W256.of_int 21323538885080684424185174689480993185750201390966223018512354418490677522148));
call{1} (ConcretePrimops.mstore_pspec m19 VK_GATE_SELECTORS_1_Y_SLOT (W256.of_int 14330561162787072568797012175184761164763459595199124517037991495673925464785));
call{1} (ConcretePrimops.mstore_pspec m18 VK_GATE_SELECTORS_1_X_SLOT (W256.of_int 15086136319636422536776088427553286399949509263897119922379735045147898875009));
call{1} (ConcretePrimops.mstore_pspec m17 VK_GATE_SELECTORS_0_Y_SLOT (W256.of_int 6190121082107679677011313308624936965782748053078710395209485205617091614781));
call{1} (ConcretePrimops.mstore_pspec m16 VK_GATE_SELECTORS_0_X_SLOT (W256.of_int 11090534100914016361232447120294745393211436081860550365760620284449885924457));
call{1} (ConcretePrimops.mstore_pspec m15 VK_GATE_SETUP_7_Y_SLOT (W256.of_int 97194583370920108185062801930585216368005987855712538133473341181290744675));
call{1} (ConcretePrimops.mstore_pspec m14 VK_GATE_SETUP_7_X_SLOT (W256.of_int 13086775255118926036233880981068687796723800497694631087151014741591951564618));
call{1} (ConcretePrimops.mstore_pspec m13 VK_GATE_SETUP_6_Y_SLOT (W256.of_int 10380438707000372753007289103897630883671902212004026295360039945231108187502));
call{1} (ConcretePrimops.mstore_pspec m12 VK_GATE_SETUP_6_X_SLOT (W256.of_int 3542620684081214281078362979824071457719243923292217179618867142734017714197));
call{1} (ConcretePrimops.mstore_pspec m11 VK_GATE_SETUP_5_Y_SLOT (W256.of_int 545412623592733862227844066395948813122937527333953380716629283051527996076));
call{1} (ConcretePrimops.mstore_pspec m10 VK_GATE_SETUP_5_X_SLOT (W256.of_int 17470132079837949645292768946901897910488674334073656384858846314172720305794));
call{1} (ConcretePrimops.mstore_pspec m9 VK_GATE_SETUP_4_Y_SLOT (W256.of_int 15424863073888926344027107060444259361026863904290125685775015743583967752523));
call{1} (ConcretePrimops.mstore_pspec m8 VK_GATE_SETUP_4_X_SLOT (W256.of_int 457576930265342335264945522969406804501107665328727087867171094316559181535));
call{1} (ConcretePrimops.mstore_pspec m7 VK_GATE_SETUP_3_Y_SLOT (W256.of_int 6787073056745945161826226704190290609825180409911049644428579916838155209697));
call{1} (ConcretePrimops.mstore_pspec m6 VK_GATE_SETUP_3_X_SLOT (W256.of_int 1869564366554527726271945732583360837778279311090061338642468249261166609475));
call{1} (ConcretePrimops.mstore_pspec m5 VK_GATE_SETUP_2_Y_SLOT (W256.of_int 5821054758250780059685638301776364871013117602597489359484409980131967326794));
call{1} (ConcretePrimops.mstore_pspec m4 VK_GATE_SETUP_2_X_SLOT (W256.of_int 1568732599965362807326380099663611053862348508639087822144187543479274466412));
call{1} (ConcretePrimops.mstore_pspec m3 VK_GATE_SETUP_1_Y_SLOT (W256.of_int 20895759739260899082484353863151962651671811489085862903974918191239970565727));
call{1} (ConcretePrimops.mstore_pspec m2 VK_GATE_SETUP_1_X_SLOT (W256.of_int 20333726085237242816528533108173405517277666887513325731527458638169740323846));
call{1} (ConcretePrimops.mstore_pspec m1 VK_GATE_SETUP_0_Y_SLOT (W256.of_int 11702890106774794311109464320829961639285524182517416836480964755620593036625));
call{1} (ConcretePrimops.mstore_pspec memory VK_GATE_SETUP_0_X_SLOT (W256.of_int 8752182643819278825281358491109311747488397345835400146720638359015287854690));
skip; progress;

rewrite /mlvk /loadVerificationKey_memory_footprint /m1 /m2 /m3 /m4 /m5 /m6 /m7 /m8 /m9 /m10 /m11 /m12 /m13 /m14 /m15 /m16 /m17 /m18 /m19 /m20 /m21 /m22 /m23 /m24 /m25 /m26 /m27 /m28 /m29 /m30 /m31 /m32 /m33 /m34 /m35 /m36 /m37 /m38 /m39 /m40 /m41;
progress;
rewrite 
/VK_GATE_SETUP_4_Y_SLOT /VK_GATE_SETUP_4_X_SLOT /VK_GATE_SETUP_3_Y_SLOT /VK_GATE_SETUP_3_X_SLOT
/VK_GATE_SETUP_2_Y_SLOT /VK_GATE_SETUP_2_X_SLOT /VK_GATE_SETUP_1_Y_SLOT /VK_GATE_SETUP_1_X_SLOT
/VK_GATE_SETUP_0_Y_SLOT /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT /VK_GATE_SETUP_7_X_SLOT
/VK_GATE_SETUP_6_Y_SLOT /VK_GATE_SETUP_6_X_SLOT /VK_GATE_SETUP_5_Y_SLOT /VK_GATE_SETUP_5_X_SLOT
/VK_GATE_SELECTORS_1_Y_SLOT /VK_GATE_SELECTORS_1_X_SLOT /VK_GATE_SELECTORS_0_Y_SLOT /VK_GATE_SELECTORS_0_X_SLOT
/VK_PERMUTATION_3_Y_SLOT /VK_PERMUTATION_3_X_SLOT /VK_PERMUTATION_2_Y_SLOT /VK_PERMUTATION_2_X_SLOT
/VK_PERMUTATION_1_Y_SLOT /VK_PERMUTATION_1_X_SLOT /VK_PERMUTATION_0_Y_SLOT /VK_PERMUTATION_0_X_SLOT
/VK_LOOKUP_TABLE_3_Y_SLOT /VK_LOOKUP_TABLE_3_X_SLOT /VK_LOOKUP_TABLE_2_Y_SLOT /VK_LOOKUP_TABLE_2_X_SLOT
/VK_LOOKUP_TABLE_1_Y_SLOT /VK_LOOKUP_TABLE_1_X_SLOT /VK_LOOKUP_TABLE_0_Y_SLOT /VK_LOOKUP_TABLE_0_X_SLOT
/VK_LOOKUP_SELECTOR_Y_SLOT /VK_LOOKUP_SELECTOR_X_SLOT /VK_LOOKUP_TABLE_TYPE_Y_SLOT /VK_LOOKUP_TABLE_TYPE_X_SLOT
/VK_RECURSIVE_FLAG_SLOT.

do 40! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 39! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 38! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 37! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 36! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 35! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 34! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 33! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 32! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 31! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 30! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 29! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 28! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 27! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 26! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 25! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 24! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 23! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 22! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 21! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 20! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 19! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 18! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 17! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 16! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 15! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 14! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 13! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 12! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 11! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 10! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 9! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 8! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 7! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 6! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 5! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 4! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 3! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 2! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
do 1! (rewrite load_store_diff; try by simplify); try (rewrite load_store_same of_uintK; by simplify).
rewrite load_store_diff; try by simplify; try (rewrite load_store_same of_uintK; by simplify).
rewrite load_store_same; by simplify.
