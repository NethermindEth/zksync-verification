pragma Goals:printall.

require import AllCore.
require import Int.
require import IntDiv.
require import AddAssignLookupLinearisationContributionWithV.
require import EvaluateLagrangePolyOutOfDomain.
require import InitializeTranscript.
require import Field.
require import FinalPairing.
require import Keccak.
require import LoadProof.
require import LoadVerificationKey.
require import PointAddIntoDest.
require import PointMulIntoDest.
require import PointMulAndAddIntoDest.
require import PrepareAggregatedCommitment.
require import PrepareQueries.
require import UInt256.
require import UpdateAggregationChallenge.
require import UpdateAggregationChallenge105.
require import Utils.
require import Verifier.
require import VerifyQuotientEvaluation.
require import YulPrimops.
require import PurePrimops.
require import Utils.
require import VerifierConsts.

import MemoryMap PurePrimops.

op vk_gate_setup_0: g.
axiom vk_gate_setup_0_F: aspoint_G1 vk_gate_setup_0 = (
    FieldQ.inF 8752182643819278825281358491109311747488397345835400146720638359015287854690,
    FieldQ.inF 11702890106774794311109464320829961639285524182517416836480964755620593036625
).
op vk_gate_setup_1: g.
axiom vk_gate_setup_1_F: aspoint_G1 vk_gate_setup_1 = (
    FieldQ.inF 20333726085237242816528533108173405517277666887513325731527458638169740323846,
    FieldQ.inF 20895759739260899082484353863151962651671811489085862903974918191239970565727
).
op vk_gate_setup_2: g.
axiom vk_gate_setup_2_F: aspoint_G1 vk_gate_setup_2 = (
    FieldQ.inF 1568732599965362807326380099663611053862348508639087822144187543479274466412,
    FieldQ.inF 5821054758250780059685638301776364871013117602597489359484409980131967326794
).
op vk_gate_setup_3: g.
axiom vk_gate_setup_3_F: aspoint_G1 vk_gate_setup_3 = (
    FieldQ.inF 1869564366554527726271945732583360837778279311090061338642468249261166609475,
    FieldQ.inF 6787073056745945161826226704190290609825180409911049644428579916838155209697
).
op vk_gate_setup_4: g.
axiom vk_gate_setup_4_F: aspoint_G1 vk_gate_setup_4 = (
    FieldQ.inF 457576930265342335264945522969406804501107665328727087867171094316559181535,
    FieldQ.inF 15424863073888926344027107060444259361026863904290125685775015743583967752523
).
op vk_gate_setup_5: g.
axiom vk_gate_setup_5_F: aspoint_G1 vk_gate_setup_5 = (
    FieldQ.inF 17470132079837949645292768946901897910488674334073656384858846314172720305794,
    FieldQ.inF 545412623592733862227844066395948813122937527333953380716629283051527996076
).
op vk_gate_setup_6: g.
axiom vk_gate_setup_6_F: aspoint_G1 vk_gate_setup_6 = (
    FieldQ.inF 3542620684081214281078362979824071457719243923292217179618867142734017714197,
    FieldQ.inF 10380438707000372753007289103897630883671902212004026295360039945231108187502
).
op vk_gate_setup_7: g.
axiom vk_gate_setup_7_F: aspoint_G1 vk_gate_setup_7 = (
    FieldQ.inF 13086775255118926036233880981068687796723800497694631087151014741591951564618,
    FieldQ.inF 97194583370920108185062801930585216368005987855712538133473341181290744675
).
op vk_gate_selectors_0: g.
axiom vk_gate_selectors_0_F: aspoint_G1 vk_gate_selectors_0 = (
    FieldQ.inF 11090534100914016361232447120294745393211436081860550365760620284449885924457,
    FieldQ.inF 6190121082107679677011313308624936965782748053078710395209485205617091614781
).
op vk_gate_selectors_1: g.
axiom vk_gate_selectors_1_F: aspoint_G1 vk_gate_selectors_1 = (
    FieldQ.inF 15086136319636422536776088427553286399949509263897119922379735045147898875009,
    FieldQ.inF 14330561162787072568797012175184761164763459595199124517037991495673925464785
).
op vk_permutation_0: g.
axiom vk_permutation_0_F: aspoint_G1 vk_permutation_0 = (
    FieldQ.inF 21323538885080684424185174689480993185750201390966223018512354418490677522148,
    FieldQ.inF 13825385863192118646834397710139923872086647553258488355179808994788744210563
).
op vk_permutation_1: g.
axiom vk_permutation_1_F: aspoint_G1 vk_permutation_1 = (
    FieldQ.inF 8390759602848414205412884900126185284679301543388803089358900543850868129488,
    FieldQ.inF 7069161667387011886642940009688789554068768218554020114127791736575843662652
).
op vk_permutation_2: g.
axiom vk_permutation_2_F: aspoint_G1 vk_permutation_2 = (
    FieldQ.inF 21779692208264067614279093821878517213862501879831804234566704419708093761485,
    FieldQ.inF 14513193766097634962386283396255157053671281137962954471134782133605379519908
).
op vk_permutation_3: g.
axiom vk_permutation_3_F: aspoint_G1 vk_permutation_3 = (
    FieldQ.inF 4751267043421347170875860608378639586591867931662910797110300384786346064625,
    FieldQ.inF 11385717438670984215358012358002661303410243223751533068904005282628107986385
).
op vk_lookup_table_0: g.
axiom vk_lookup_table_0_F: aspoint_G1 vk_lookup_table_0 = (
    FieldQ.inF 20045313662746578028950791395157660351198208045597010788369662325700141348443,
    FieldQ.inF 2200761695078532224145807378118591946349840073460005094399078719163643466856
).
op vk_lookup_table_1: g.
axiom vk_lookup_table_1_F: aspoint_G1 vk_lookup_table_1 = (
    FieldQ.inF 13866646217607640441607041956684111087071997201218815349460750486791109380780,
    FieldQ.inF 13178446611795019678701878053235714968797421377761816259103804833273256298333
).
op vk_lookup_table_2: g.
axiom vk_lookup_table_2_F: aspoint_G1 vk_lookup_table_2 = (
    FieldQ.inF 5057503605752869531452842486824745179648819794307492731589448195268672785801,
    FieldQ.inF 8597434312520299647191152876265164941580478223412397470356037586993894367875
).
op vk_lookup_table_3: g.
axiom vk_lookup_table_3_F: aspoint_G1 vk_lookup_table_3 = (
    FieldQ.inF 1342318055425277544055386589364579054544440640110901993487861472578322387903,
    FieldQ.inF 4438354282468267034382897187461199764068502038746983055473062465446039509158
).
op vk_lookup_selector: g.
axiom vk_lookup_selector_F: aspoint_G1 vk_lookup_selector = (
    FieldQ.inF 21714794642552531775933093644480516421064284615960245486122726724547638127878,
    FieldQ.inF 20374981665942106195451736226451722737514281476778224282304648903722926579601
).
op vk_lookup_table_type: g.
axiom vk_lookup_table_type_F: aspoint_G1 vk_lookup_table_type = (
    FieldQ.inF 196778531949039689886328474582670216324308721975620885373710029662715787742,
    FieldQ.inF 11005776646725047106517461026899305486268481542412200771754169232553006481646
).

op commit_fr (state: int*int) (input: FieldR.F): int*int =  (
  keccakT 0 state.`1 state.`2 (FieldR.asint input),
  keccakT 1 state.`1 state.`2 (FieldR.asint input)
).

op commit_g (state: int*int) (input: g): int*int = 
  let s1 = keccakT 0 state.`1 state.`2 (F_to_int_point (aspoint_G1 input)).`1 in
  let s2 = keccakT 1 state.`1 state.`2 (F_to_int_point (aspoint_G1 input)).`1 in
(
  keccakT 0 s1 s2 (F_to_int_point (aspoint_G1 input)).`2,
  keccakT 1 s1 s2 (F_to_int_point (aspoint_G1 input)).`2
).

op get_commitment (state: int*int) (index: int): FieldR.F = FieldR.inF ((keccakC 2 state.`1 state.`2 index) %% (2^253)).

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
  
  proc mid (public_input_length_in_words: int, public_input: int, proof_length_in_words: int, state_poly_0: int*int, state_poly_1: int*int, state_poly_2: int*int, state_poly_3: int*int, copy_permutation_grand_product: int*int, lookup_s_poly: int*int, lookup_grand_product: int*int, quotient_poly_part_0: int*int, quotient_poly_part_1: int*int, quotient_poly_part_2: int*int, quotient_poly_part_3: int*int, state_poly_0_opening_at_z: int, state_poly_1_opening_at_z: int, state_poly_2_opening_at_z: int, state_poly_3_opening_at_z: int, state_poly_3_opening_at_z_omega: int, gate_selector_0_opening_at_z: int, copy_permutation_poly_0_opening_at_z: int, copy_permutation_poly_1_opening_at_z: int, copy_permutation_poly_2_opening_at_z: int, copy_permutation_grand_product_opening_at_z_omega: int, lookup_s_poly_opening_at_z_omega: int, lookup_grand_product_opening_at_z_omega: int, lookup_t_poly_opening_at_z: int, lookup_t_poly_opening_at_z_omega: int, lookup_selector_poly_opening_at_z: int, lookup_table_type_poly_opening_at_z: int, quotient_poly_opening_at_z: int, linearisation_poly_opening_at_z: int, opening_proof_at_z: int*int, opening_proof_at_z_omega: int*int, recursive_proof_length_in_words: int, recursive_part_p1: int*int, recursive_part_p2: int*int) : bool = {
   
   var initial_state_0 <- 0;
   var initial_state_1 <- 0;
  
   (* load proof related *)
   var load_proof_opt;
   
   (* load proof mod *)
   var _public_input, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, 
       _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, 
       _copy_permutation_grand_product_opening_at_z_omega, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, 
       _lookup_t_poly_opening_at_z, _lookup_t_poly_opening_at_z_omega, _lookup_selector_poly_opening_at_z, _lookup_table_type_poly_opening_at_z, 
       _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z : int; 
   var _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, _quotient_poly_part_0, 
       _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _opening_proof_at_z, _opening_proof_at_z_omega: int*int;
   var _recursive_part_p1, _recursive_part_p2: (int*int) option;
    
   (* load verification key related *)
   var vk_gate_setup_0X, vk_gate_setup_0Y,
       vk_gate_setup_1X, vk_gate_setup_1Y,
       vk_gate_setup_2X, vk_gate_setup_2Y,
       vk_gate_setup_3X, vk_gate_setup_3Y,
       vk_gate_setup_4X, vk_gate_setup_4Y,
       vk_gate_setup_5X, vk_gate_setup_5Y,
       vk_gate_setup_6X, vk_gate_setup_6Y,
       vk_gate_setup_7X, vk_gate_setup_7Y : int;
   var vk_gate_selectors_0X, vk_gate_selectors_1X, 
       vk_gate_selectors_0Y, vk_gate_selectors_1Y: int;
   var vk_permutation_0X, vk_permutation_0Y, 
       vk_permutation_1X, vk_permutation_1Y, 
       vk_permutation_2X, vk_permutation_2Y, 
       vk_permutation_3X, vk_permutation_3Y: int;
   var vk_lookup_table_0X, vk_lookup_table_0Y,
       vk_lookup_table_1X, vk_lookup_table_1Y,
       vk_lookup_table_2X, vk_lookup_table_2Y,
       vk_lookup_table_3X, vk_lookup_table_3Y: int;
   var vk_lookup_selector_X, vk_lookup_selector_Y: int;
   var vk_lookup_table_type_X, vk_lookup_table_type_Y: int;
   var vk_recursive_flag: bool;

   (* initialize transcript *)
   var state_alpha, state_beta, state_gamma, state_eta;
   var state_beta_lookup, state_gamma_lookup; 
   var state_z, state_z_in_domain, state_v, state_u;

   (* verify quotient evaluation *)
   var alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8;
   var l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega;
   var verify_quotient_evaluation_opt;

   (* prepare queries *)
   var prepare_queries_opt;
   var query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookup_s_first_aggregated_commitment,
       lookup_grand_product_first_aggregated_coefficient, query_t_poly_aggregated;

   (* prepare aggregated commitment *)
   var prepare_aggregated_commitment_opt;
   var aggregated_at_z, aggregated_opening_at_z, aggregated_at_z_omega, aggregated_opening_at_z_omega, pairing_pair_with_generator, pairing_buffer_point;
   
   (* final pairing *)
   var final_pairing_bool;  

   var failed;
   failed <- false;

    (* _loadVerificationKeys *)
    vk_gate_setup_0X <- 8752182643819278825281358491109311747488397345835400146720638359015287854690;
    vk_gate_setup_0Y <- 11702890106774794311109464320829961639285524182517416836480964755620593036625;
    vk_gate_setup_1X <- 20333726085237242816528533108173405517277666887513325731527458638169740323846;
    vk_gate_setup_1Y <- 20895759739260899082484353863151962651671811489085862903974918191239970565727;
    vk_gate_setup_2X <- 1568732599965362807326380099663611053862348508639087822144187543479274466412;
    vk_gate_setup_2Y <- 5821054758250780059685638301776364871013117602597489359484409980131967326794;
    vk_gate_setup_3X <- 1869564366554527726271945732583360837778279311090061338642468249261166609475;
    vk_gate_setup_3Y <- 6787073056745945161826226704190290609825180409911049644428579916838155209697;
    vk_gate_setup_4X <- 457576930265342335264945522969406804501107665328727087867171094316559181535;
    vk_gate_setup_4Y <- 15424863073888926344027107060444259361026863904290125685775015743583967752523;
    vk_gate_setup_5X <- 17470132079837949645292768946901897910488674334073656384858846314172720305794;
    vk_gate_setup_5Y <- 545412623592733862227844066395948813122937527333953380716629283051527996076;
    vk_gate_setup_6X <- 3542620684081214281078362979824071457719243923292217179618867142734017714197;
    vk_gate_setup_6Y <- 10380438707000372753007289103897630883671902212004026295360039945231108187502;
    vk_gate_setup_7X <- 13086775255118926036233880981068687796723800497694631087151014741591951564618;
    vk_gate_setup_7Y <- 97194583370920108185062801930585216368005987855712538133473341181290744675;
    
    vk_gate_selectors_0X <- 11090534100914016361232447120294745393211436081860550365760620284449885924457;
    vk_gate_selectors_0Y <- 6190121082107679677011313308624936965782748053078710395209485205617091614781;
    vk_gate_selectors_1X <- 15086136319636422536776088427553286399949509263897119922379735045147898875009;
    vk_gate_selectors_1Y <- 14330561162787072568797012175184761164763459595199124517037991495673925464785;

    vk_permutation_0X <- 21323538885080684424185174689480993185750201390966223018512354418490677522148;
    vk_permutation_0Y <- 13825385863192118646834397710139923872086647553258488355179808994788744210563;
    vk_permutation_1X <- 8390759602848414205412884900126185284679301543388803089358900543850868129488;
    vk_permutation_1Y <- 7069161667387011886642940009688789554068768218554020114127791736575843662652;
    vk_permutation_2X <- 21779692208264067614279093821878517213862501879831804234566704419708093761485;
    vk_permutation_2Y <- 14513193766097634962386283396255157053671281137962954471134782133605379519908;
    vk_permutation_3X <- 4751267043421347170875860608378639586591867931662910797110300384786346064625;
    vk_permutation_3Y <- 11385717438670984215358012358002661303410243223751533068904005282628107986385;

    vk_lookup_table_0X <- 20045313662746578028950791395157660351198208045597010788369662325700141348443;
    vk_lookup_table_0Y <- 2200761695078532224145807378118591946349840073460005094399078719163643466856;
    vk_lookup_table_1X <- 13866646217607640441607041956684111087071997201218815349460750486791109380780;
    vk_lookup_table_1Y <- 13178446611795019678701878053235714968797421377761816259103804833273256298333;
    vk_lookup_table_2X <- 5057503605752869531452842486824745179648819794307492731589448195268672785801;
    vk_lookup_table_2Y <- 8597434312520299647191152876265164941580478223412397470356037586993894367875;
    vk_lookup_table_3X <- 1342318055425277544055386589364579054544440640110901993487861472578322387903;
    vk_lookup_table_3Y <- 4438354282468267034382897187461199764068502038746983055473062465446039509158;

    vk_lookup_selector_X <- 21714794642552531775933093644480516421064284615960245486122726724547638127878;
    vk_lookup_selector_Y <- 20374981665942106195451736226451722737514281476778224282304648903722926579601;

    vk_lookup_table_type_X <- 196778531949039689886328474582670216324308721975620885373710029662715787742;
    vk_lookup_table_type_Y <- 11005776646725047106517461026899305486268481542412200771754169232553006481646;
    
    vk_recursive_flag <- false;
    
    load_proof_opt <@ LoadProof.mid(public_input_length_in_words, public_input, proof_length_in_words, state_poly_0, state_poly_1, state_poly_2, state_poly_3, copy_permutation_grand_product, lookup_s_poly, lookup_grand_product, quotient_poly_part_0, quotient_poly_part_1, quotient_poly_part_2, quotient_poly_part_3, state_poly_0_opening_at_z, state_poly_1_opening_at_z, state_poly_2_opening_at_z, state_poly_3_opening_at_z, state_poly_3_opening_at_z_omega, gate_selector_0_opening_at_z, copy_permutation_poly_0_opening_at_z, copy_permutation_poly_1_opening_at_z, copy_permutation_poly_2_opening_at_z, copy_permutation_grand_product_opening_at_z_omega, lookup_s_poly_opening_at_z_omega, lookup_grand_product_opening_at_z_omega, lookup_t_poly_opening_at_z, lookup_t_poly_opening_at_z_omega, lookup_selector_poly_opening_at_z, lookup_table_type_poly_opening_at_z, quotient_poly_opening_at_z, linearisation_poly_opening_at_z, opening_proof_at_z, opening_proof_at_z_omega, recursive_proof_length_in_words, vk_recursive_flag, recursive_part_p1, recursive_part_p2);
    failed <- failed \/ is_none load_proof_opt;
    (_public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product,
     _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z,
     _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z,
     _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_s_poly_opening_at_z_omega,
     _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_t_poly_opening_at_z_omega, _lookup_selector_poly_opening_at_z,
     _lookup_table_type_poly_opening_at_z, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega,
     _recursive_part_p1, _recursive_part_p2) <- oget load_proof_opt;

    (* initials1 and initials2 should be 0? *)
    (state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_eta, state_z, state_z_in_domain, state_v, state_u) <@ InitializeTranscript.mid(initial_state_0, initial_state_1, _public_input, _state_poly_0.`1, _state_poly_0.`2, _state_poly_1.`1, _state_poly_1.`2, _state_poly_2.`1, _state_poly_2.`2, _state_poly_3.`1, _state_poly_3.`2, _lookup_s_poly.`1, _lookup_s_poly.`2, _copy_permutation_grand_product.`1, _copy_permutation_grand_product.`2, _lookup_grand_product.`1, _lookup_grand_product.`2, _quotient_poly_part_0.`1, _quotient_poly_part_0.`2, _quotient_poly_part_1.`1, _quotient_poly_part_1.`2, _quotient_poly_part_2.`1, _quotient_poly_part_2.`2, _quotient_poly_part_3.`1, _quotient_poly_part_3.`2, _quotient_poly_opening_at_z, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_selector_poly_opening_at_z, _lookup_table_type_poly_opening_at_z, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z_omega, _linearisation_poly_opening_at_z, _opening_proof_at_z.`1, _opening_proof_at_z.`2, _opening_proof_at_z_omega.`1, _opening_proof_at_z_omega.`2);
    
    (verify_quotient_evaluation_opt, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega) <@ VerifyQuotientEvaluation.mid(state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_z, _public_input, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _gate_selector_0_opening_at_z, _linearisation_poly_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, state_z_in_domain, _quotient_poly_opening_at_z);
    failed <- failed \/ !(odflt false verify_quotient_evaluation_opt);

    prepare_queries_opt <@ PrepareQueries.mid(state_z_in_domain, _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, (vk_lookup_table_0X, vk_lookup_table_0Y), (vk_lookup_table_1X, vk_lookup_table_1Y), (vk_lookup_table_2X, vk_lookup_table_2Y), (vk_lookup_table_3X, vk_lookup_table_3Y), state_eta, (vk_gate_setup_0X, vk_gate_setup_0Y), (vk_gate_setup_1X, vk_gate_setup_1Y), (vk_gate_setup_2X, vk_gate_setup_2Y), (vk_gate_setup_3X, vk_gate_setup_3Y), (vk_gate_setup_4X, vk_gate_setup_4Y), (vk_gate_setup_5X, vk_gate_setup_5Y), (vk_gate_setup_6X, vk_gate_setup_6Y), (vk_gate_setup_7X, vk_gate_setup_7Y), _state_poly_3_opening_at_z_omega, state_v, state_z, _gate_selector_0_opening_at_z, state_alpha, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, state_beta, state_gamma, (vk_gate_selectors_1X, vk_gate_selectors_1Y), (vk_permutation_3X, vk_permutation_3Y), _copy_permutation_grand_product_opening_at_z_omega, l0_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _lookup_grand_product_opening_at_z_omega, z_minus_last_omega, _lookup_t_poly_opening_at_z_omega, state_beta_lookup, _lookup_t_poly_opening_at_z, beta_gamma_plus_gamma, _lookup_table_type_poly_opening_at_z, _lookup_selector_poly_opening_at_z, state_gamma_lookup, beta_plus_one, ln_minus_one_at_z);
    failed <- failed \/ is_none prepare_queries_opt;
    (query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookup_s_first_aggregated_commitment, lookup_grand_product_first_aggregated_coefficient, query_t_poly_aggregated) <- oget prepare_queries_opt;

    prepare_aggregated_commitment_opt <@ PrepareAggregatedCommitment.mid(query_at_z_0, _quotient_poly_opening_at_z, query_at_z_1, state_v, _linearisation_poly_opening_at_z, _state_poly_0, _state_poly_0_opening_at_z, _state_poly_1, _state_poly_1_opening_at_z, _state_poly_2, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, (vk_gate_selectors_0X, vk_gate_selectors_0Y), _gate_selector_0_opening_at_z, (vk_permutation_0X, vk_permutation_0Y), _copy_permutation_poly_0_opening_at_z, (vk_permutation_1X, vk_permutation_1Y), _copy_permutation_poly_1_opening_at_z, (vk_permutation_2X, vk_permutation_2Y), _copy_permutation_poly_2_opening_at_z, _lookup_t_poly_opening_at_z, (vk_lookup_selector_X, vk_lookup_selector_Y), _lookup_selector_poly_opening_at_z, (vk_lookup_table_type_X, vk_lookup_table_type_Y), _lookup_table_type_poly_opening_at_z, copy_permutation_first_aggregated_commitment_coeff, state_u, _copy_permutation_grand_product, _copy_permutation_grand_product_opening_at_z_omega, _state_poly_3, _state_poly_3_opening_at_z_omega, _lookup_s_poly, _lookup_s_poly_opening_at_z_omega, lookup_s_first_aggregated_commitment, _lookup_grand_product, _lookup_grand_product_opening_at_z_omega, lookup_grand_product_first_aggregated_coefficient, query_t_poly_aggregated, _lookup_t_poly_opening_at_z_omega);
   failed <- failed \/ is_none prepare_aggregated_commitment_opt;
   (aggregated_at_z, aggregated_opening_at_z, aggregated_at_z_omega, aggregated_opening_at_z_omega, pairing_pair_with_generator, pairing_buffer_point) <- oget prepare_aggregated_commitment_opt;

  final_pairing_bool <@ FinalPairing.mid(state_u, state_z, pairing_pair_with_generator, pairing_buffer_point, _opening_proof_at_z, _opening_proof_at_z_omega, vk_recursive_flag, oget _recursive_part_p1, oget _recursive_part_p2);
  failed <- failed \/ !final_pairing_bool;
   
  return !failed;
 }

  proc high_encapsulated (public_input_length_in_words: int, public_input: FieldR.F, proof_length_in_words: int, state_poly_0: g, state_poly_1: g, state_poly_2: g, state_poly_3: g, copy_permutation_grand_product: g, lookup_s_poly: g, lookup_grand_product: g, quotient_poly_part_0: g, quotient_poly_part_1: g, quotient_poly_part_2: g, quotient_poly_part_3: g, state_poly_0_opening_at_z: FieldR.F, state_poly_1_opening_at_z: FieldR.F, state_poly_2_opening_at_z: FieldR.F, state_poly_3_opening_at_z: FieldR.F, state_poly_3_opening_at_z_omega: FieldR.F, gate_selector_0_opening_at_z: FieldR.F, copy_permutation_poly_0_opening_at_z: FieldR.F, copy_permutation_poly_1_opening_at_z: FieldR.F, copy_permutation_poly_2_opening_at_z: FieldR.F, copy_permutation_grand_product_opening_at_z_omega: FieldR.F, lookup_s_poly_opening_at_z_omega: FieldR.F, lookup_grand_product_opening_at_z_omega: FieldR.F, lookup_t_poly_opening_at_z: FieldR.F, lookup_t_poly_opening_at_z_omega: FieldR.F, lookup_selector_poly_opening_at_z: FieldR.F, lookup_table_type_poly_opening_at_z: FieldR.F, quotient_poly_opening_at_z: FieldR.F, linearisation_poly_opening_at_z: FieldR.F, opening_proof_at_z: g, opening_proof_at_z_omega: g, recursive_proof_length_in_words: int, recursive_part_p1: g, recursive_part_p2: g) : bool = {
     
   (* load proof related *)
   var load_proof_opt;
   
   (* load proof mod *)
   var _public_input, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, 
       _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, 
       _copy_permutation_grand_product_opening_at_z_omega, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, 
       _lookup_t_poly_opening_at_z, _lookup_t_poly_opening_at_z_omega, _lookup_selector_poly_opening_at_z, _lookup_table_type_poly_opening_at_z, 
       _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z : FieldR.F; 
   var _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, _quotient_poly_part_0, 
       _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _opening_proof_at_z, _opening_proof_at_z_omega: g;
   var _recursive_part_p1, _recursive_part_p2: g option;
    
   (* load verification key related *)
   var vk_recursive_flag: bool;

   (* initialize transcript *)
   var state_alpha, state_beta, state_gamma, state_eta;
   var state_beta_lookup, state_gamma_lookup; 
   var state_z, state_z_in_domain, state_v, state_u;

   (* verify quotient evaluation *)
   var alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8;
   var l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega;
   var verify_quotient_evaluation_opt;

   (* prepare queries *)
   var query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment,
       lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated;

   (* prepare aggregated commitment *)
   var aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, aggregatedOpeningAtZOmega, pairingPairWithGeneratorSlot, pairingBufferPointSlot;
   
   (* final pairing *)
   var final_pairing_bool;  

   var failed;
   failed <- false;
   
    vk_recursive_flag <- false;
    
    load_proof_opt <@ LoadProof.high(public_input_length_in_words, public_input, proof_length_in_words, state_poly_0, state_poly_1, state_poly_2, state_poly_3, copy_permutation_grand_product, lookup_s_poly, lookup_grand_product, quotient_poly_part_0, quotient_poly_part_1, quotient_poly_part_2, quotient_poly_part_3, state_poly_0_opening_at_z, state_poly_1_opening_at_z, state_poly_2_opening_at_z, state_poly_3_opening_at_z, state_poly_3_opening_at_z_omega, gate_selector_0_opening_at_z, copy_permutation_poly_0_opening_at_z, copy_permutation_poly_1_opening_at_z, copy_permutation_poly_2_opening_at_z, copy_permutation_grand_product_opening_at_z_omega, lookup_s_poly_opening_at_z_omega, lookup_grand_product_opening_at_z_omega, lookup_t_poly_opening_at_z, lookup_t_poly_opening_at_z_omega, lookup_selector_poly_opening_at_z, lookup_table_type_poly_opening_at_z, quotient_poly_opening_at_z, linearisation_poly_opening_at_z, opening_proof_at_z, opening_proof_at_z_omega, recursive_proof_length_in_words, vk_recursive_flag, recursive_part_p1, recursive_part_p2);
    failed <- failed \/ is_none load_proof_opt;
    (_public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product,
     _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z,
     _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z,
     _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_s_poly_opening_at_z_omega,
     _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_t_poly_opening_at_z_omega, _lookup_selector_poly_opening_at_z,
     _lookup_table_type_poly_opening_at_z, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega,
     _recursive_part_p1, _recursive_part_p2) <- oget load_proof_opt;

    (* initials1 and initials2 should be 0? *)
    (state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_eta, state_z, state_z_in_domain, state_v, state_u) <@ InitializeTranscript.high(0, 0, _public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _lookup_s_poly, _copy_permutation_grand_product, _lookup_grand_product, _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _quotient_poly_opening_at_z, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_selector_poly_opening_at_z, _lookup_table_type_poly_opening_at_z, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z_omega, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega);
    
    (verify_quotient_evaluation_opt, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega) <@ VerifyQuotientEvaluation.high(state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_z, _public_input, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _gate_selector_0_opening_at_z, _linearisation_poly_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, state_z_in_domain, _quotient_poly_opening_at_z);
    failed <- failed \/ !(odflt false verify_quotient_evaluation_opt);

    (query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated) <@ PrepareQueries.high(state_z_in_domain, _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, vk_lookup_table_0, vk_lookup_table_1, vk_lookup_table_2, vk_lookup_table_3, state_eta, vk_gate_setup_0, vk_gate_setup_1, vk_gate_setup_2, vk_gate_setup_3, vk_gate_setup_4, vk_gate_setup_5, vk_gate_setup_6, vk_gate_setup_7, _state_poly_3_opening_at_z_omega, state_v, state_z, _gate_selector_0_opening_at_z, state_alpha, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, state_beta, state_gamma, vk_gate_selectors_1, vk_permutation_3, _copy_permutation_grand_product_opening_at_z_omega, l0_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _lookup_grand_product_opening_at_z_omega, z_minus_last_omega, _lookup_t_poly_opening_at_z_omega, state_beta_lookup, _lookup_t_poly_opening_at_z, beta_gamma_plus_gamma, _lookup_table_type_poly_opening_at_z, _lookup_selector_poly_opening_at_z, state_gamma_lookup, beta_plus_one, ln_minus_one_at_z);

    (aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, aggregatedOpeningAtZOmega, pairingPairWithGeneratorSlot, pairingBufferPointSlot) <@ PrepareAggregatedCommitment.high(query_at_z_0, _quotient_poly_opening_at_z, query_at_z_1, state_v, _linearisation_poly_opening_at_z, _state_poly_0, _state_poly_0_opening_at_z, _state_poly_1, _state_poly_1_opening_at_z, _state_poly_2, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, vk_gate_selectors_0, _gate_selector_0_opening_at_z, vk_permutation_0, _copy_permutation_poly_0_opening_at_z, vk_permutation_1, _copy_permutation_poly_1_opening_at_z, vk_permutation_2, _copy_permutation_poly_2_opening_at_z, _lookup_t_poly_opening_at_z, vk_lookup_selector, _lookup_selector_poly_opening_at_z, vk_lookup_table_type, _lookup_table_type_poly_opening_at_z, copy_permutation_first_aggregated_commitment_coeff, state_u, _copy_permutation_grand_product, _copy_permutation_grand_product_opening_at_z_omega, _state_poly_3, _state_poly_3_opening_at_z_omega, _lookup_s_poly, _lookup_s_poly_opening_at_z_omega, lookupSFirstAggregatedCommitment, _lookup_grand_product, _lookup_grand_product_opening_at_z_omega, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated, _lookup_t_poly_opening_at_z_omega);

  final_pairing_bool <@ FinalPairing.high(state_u, state_z, pairingPairWithGeneratorSlot, pairingBufferPointSlot, _opening_proof_at_z, _opening_proof_at_z_omega, vk_recursive_flag, oget _recursive_part_p1, oget _recursive_part_p2);
  failed <- failed \/ !final_pairing_bool;
   
  return !failed;
  }

  proc super_high (
    public_input_length_in_words: int,
    public_input: FieldR.F,
    proof_length_in_words: int,
    state_poly_0: g,
    state_poly_1: g,
    state_poly_2: g,
    state_poly_3: g,
    copy_permutation_grand_product: g,
    lookup_s_poly: g,
    lookup_grand_product: g,
    quotient_poly_part_0: g,
    quotient_poly_part_1: g,
    quotient_poly_part_2: g,
    quotient_poly_part_3: g,
    state_poly_0_opening_at_z: FieldR.F,
    state_poly_1_opening_at_z: FieldR.F,
    state_poly_2_opening_at_z: FieldR.F,
    state_poly_3_opening_at_z: FieldR.F,
    state_poly_3_opening_at_z_omega: FieldR.F,
    gate_selector_0_opening_at_z: FieldR.F,
    copy_permutation_poly_0_opening_at_z: FieldR.F,
    copy_permutation_poly_1_opening_at_z: FieldR.F,
    copy_permutation_poly_2_opening_at_z: FieldR.F,
    copy_permutation_grand_product_opening_at_z_omega: FieldR.F,
    lookup_s_poly_opening_at_z_omega: FieldR.F,
    lookup_grand_product_opening_at_z_omega: FieldR.F,
    lookup_t_poly_opening_at_z: FieldR.F,
    lookup_t_poly_opening_at_z_omega: FieldR.F,
    lookup_selector_poly_opening_at_z: FieldR.F,
    lookup_table_type_poly_opening_at_z: FieldR.F,
    quotient_poly_opening_at_z: FieldR.F,
    linearisation_poly_opening_at_z: FieldR.F,
    opening_proof_at_z: g,
    opening_proof_at_z_omega: g,
    recursive_proof_length_in_words: int,
    recursive_part_p1: g,
    recursive_part_p2: g
  ) : bool = {
     
   (* load proof related *)
   var load_proof_opt;
   
   (* load proof mod *)
   var _public_input, a_at_z, b_at_z, c_at_z, d_at_z, d_at_z_omega, 
       main_gate_selector_at_z, sigma_0_at_z, sigma_1_at_z, sigma_2_at_z, 
       z_perm_at_z_omega, _lookup_s_poly_opening_at_z_omega, z_lookup_at_z_omega, 
       t_at_z, t_at_z_omega, lookup_selector_at_z, table_type_at_z, 
       _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z : FieldR.F; 
   var _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, t_0, t_1, t_2, t_3, _opening_proof_at_z, _opening_proof_at_z_omega: g;
   var _recursive_part_p1, _recursive_part_p2: g option;
    
   (* load verification key related *)
   var vk_recursive_flag: bool;

   (* initialize transcript *)
   var alpha, beta_, gamma, eta_;
   var beta', gamma'; 
   var z, z_in_domain, v, u;

   (* verify quotient evaluation *)
   var alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8;
   var l_0_at_z, l_n_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega;
   var verify_quotient_evaluation_opt;

   (* prepare queries *)
   var query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated;

   (* prepare aggregated commitment *)
   var aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, aggregatedOpeningAtZOmega, pairingPairWithGeneratorSlot, pairingBufferPointSlot;
   
   (* final pairing *)
   var final_pairing_bool;  

   var failed;
   var q_a, q_b, q_c, q_d, q_ab, q_ac, q_const, q_d_next, custom_gate_selector, sigma_3, col_0, col_1, col_2, col_3: g;
    failed <- false;
    q_a <- vk_gate_setup_0;
    q_b <- vk_gate_setup_1;
    q_c <- vk_gate_setup_2;
    q_d <- vk_gate_setup_3;
    q_ab <- vk_gate_setup_4;
    q_ac <- vk_gate_setup_5;
    q_const <- vk_gate_setup_6;
    q_d_next <- vk_gate_setup_7;
    custom_gate_selector <- vk_gate_selectors_1;
    sigma_3 <- vk_permutation_3;
    col_0 <- vk_lookup_table_0;
    col_1 <- vk_lookup_table_1;
    col_2 <- vk_lookup_table_2;
    col_3 <- vk_lookup_table_3;
    vk_recursive_flag <- false;
    
    load_proof_opt <@ LoadProof.high(public_input_length_in_words, public_input, proof_length_in_words, state_poly_0, state_poly_1, state_poly_2, state_poly_3, copy_permutation_grand_product, lookup_s_poly, lookup_grand_product, quotient_poly_part_0, quotient_poly_part_1, quotient_poly_part_2, quotient_poly_part_3, state_poly_0_opening_at_z, state_poly_1_opening_at_z, state_poly_2_opening_at_z, state_poly_3_opening_at_z, state_poly_3_opening_at_z_omega, gate_selector_0_opening_at_z, copy_permutation_poly_0_opening_at_z, copy_permutation_poly_1_opening_at_z, copy_permutation_poly_2_opening_at_z, copy_permutation_grand_product_opening_at_z_omega, lookup_s_poly_opening_at_z_omega, lookup_grand_product_opening_at_z_omega, lookup_t_poly_opening_at_z, lookup_t_poly_opening_at_z_omega, lookup_selector_poly_opening_at_z, lookup_table_type_poly_opening_at_z, quotient_poly_opening_at_z, linearisation_poly_opening_at_z, opening_proof_at_z, opening_proof_at_z_omega, recursive_proof_length_in_words, vk_recursive_flag, recursive_part_p1, recursive_part_p2);
    failed <- failed \/ is_none load_proof_opt;
    (_public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product,
     t_0, t_1, t_2, t_3, a_at_z, b_at_z, c_at_z, d_at_z, d_at_z_omega, main_gate_selector_at_z, sigma_0_at_z, sigma_1_at_z, sigma_2_at_z, z_perm_at_z_omega, _lookup_s_poly_opening_at_z_omega,
     z_lookup_at_z_omega, t_at_z, t_at_z_omega, lookup_selector_at_z,
     table_type_at_z, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega,
     _recursive_part_p1, _recursive_part_p2) <- oget load_proof_opt;

    (* initials1 and initials2 should be 0? *)
    (alpha, beta_, beta', gamma, gamma', eta_, z, z_in_domain, v, u) <@ InitializeTranscript.high(0, 0, _public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _lookup_s_poly, _copy_permutation_grand_product, _lookup_grand_product, t_0, t_1, t_2, t_3, _quotient_poly_opening_at_z, a_at_z, b_at_z, c_at_z, d_at_z, d_at_z_omega, main_gate_selector_at_z, sigma_0_at_z, sigma_1_at_z, sigma_2_at_z, z_perm_at_z_omega, t_at_z, lookup_selector_at_z, table_type_at_z, _lookup_s_poly_opening_at_z_omega, z_lookup_at_z_omega, t_at_z_omega, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega);
    
    (verify_quotient_evaluation_opt, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, l_0_at_z, l_n_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega) <@ VerifyQuotientEvaluation.high(alpha, beta_, beta', gamma, gamma', z, _public_input, sigma_0_at_z, sigma_1_at_z, sigma_2_at_z, a_at_z, b_at_z, c_at_z, d_at_z, _lookup_s_poly_opening_at_z_omega, z_lookup_at_z_omega, main_gate_selector_at_z, _linearisation_poly_opening_at_z, z_perm_at_z_omega, z_in_domain, _quotient_poly_opening_at_z);
    failed <- failed \/ !(odflt false verify_quotient_evaluation_opt);

    (query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated) <@ PrepareQueries.super_high(
      alpha,
      beta_,
      gamma,
      v,
      z,
      Constants.DOMAIN_SIZE,
      t_0,
      t_1,
      t_2,
      t_3,
      main_gate_selector_at_z,
      a_at_z,
      b_at_z,
      c_at_z,
      d_at_z,
      q_a,
      q_b,
      q_c,
      q_d,
      q_ab,
      q_ac,
      q_const,
      q_d_next,
      d_at_z_omega,
      custom_gate_selector,
      z_perm_at_z_omega,
      sigma_0_at_z,
      sigma_1_at_z,
      sigma_2_at_z,
      sigma_3,
      FieldR.inF Constants.NON_RESIDUE_0,
      FieldR.inF Constants.NON_RESIDUE_1,
      FieldR.inF Constants.NON_RESIDUE_2,
      l_0_at_z,
      Constants.OMEGAFr,
      z_lookup_at_z_omega,
      col_0,
      col_1,
      col_2,
      col_3,
      eta_,
      lookup_selector_at_z,
      table_type_at_z,
      beta',
      gamma',
      t_at_z,
      t_at_z_omega,
      l_n_minus_one_at_z
    );

    (aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, aggregatedOpeningAtZOmega, pairingPairWithGeneratorSlot, pairingBufferPointSlot) <@ PrepareAggregatedCommitment.super_high(query_at_z_0, _quotient_poly_opening_at_z, query_at_z_1, v, _linearisation_poly_opening_at_z, _state_poly_0, a_at_z, _state_poly_1, b_at_z, _state_poly_2, c_at_z, d_at_z, vk_gate_selectors_0, main_gate_selector_at_z, vk_permutation_0, sigma_0_at_z, vk_permutation_1, sigma_1_at_z, vk_permutation_2, sigma_2_at_z, t_at_z, vk_lookup_selector, lookup_selector_at_z, vk_lookup_table_type, table_type_at_z, copy_permutation_first_aggregated_commitment_coeff, u, _copy_permutation_grand_product, z_perm_at_z_omega, _state_poly_3, d_at_z_omega, _lookup_s_poly, _lookup_s_poly_opening_at_z_omega, lookupSFirstAggregatedCommitment, _lookup_grand_product, z_lookup_at_z_omega, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated, t_at_z_omega);

    final_pairing_bool <@ FinalPairing.high(u, z, pairingPairWithGeneratorSlot, pairingBufferPointSlot, _opening_proof_at_z, _opening_proof_at_z_omega, vk_recursive_flag, oget _recursive_part_p1, oget _recursive_part_p2);
    failed <- failed \/ !final_pairing_bool;
   
    return !failed;
  }

  proc high (
    public_input_length_in_words: int,
    public_input: FieldR.F,
    proof_length_in_words: int,
    a: g,
    b: g,
    c: g,
    d: g,
    z_perm: g,
    s: g,
    z_lookup: g,
    t_0: g,
    t_1: g,
    t_2: g,
    t_3: g,
    a_at_z: FieldR.F,
    b_at_z: FieldR.F,
    c_at_z: FieldR.F,
    d_at_z: FieldR.F,
    d_at_z_omega: FieldR.F,
    main_gate_selector_at_z: FieldR.F,
    sigma_0_at_z: FieldR.F,
    sigma_1_at_z: FieldR.F,
    sigma_2_at_z: FieldR.F,
    z_perm_at_z_omega: FieldR.F,
    s_at_z_omega: FieldR.F,
    z_lookup_at_z_omega: FieldR.F,
    t_at_z: FieldR.F,
    t_at_z_omega: FieldR.F,
    lookup_selector_at_z: FieldR.F,
    table_type_at_z: FieldR.F,
    quotient_poly_opening_at_z: FieldR.F,
    r_at_z: FieldR.F,
    w: g,
    w': g,
    recursive_proof_length_in_words: int,
    recursive_part_p1: g,
    recursive_part_p2: g
  ) : bool = {
    
    var isValid;
    var state: int*int;
    var state0_0, state1_0, state0_1, state1_1, state0_2, state1_2, state0_3, state1_3,
        state0_4, state1_4, state0_5, state1_5, state0_6, state1_6, state0_7, state1_7,
        state0_8, state1_8, state0_9, state1_9, state0_10, state1_10, state0_11, state1_11,
        state0_12, state1_12, state0_13, state1_13, state0_14, state1_14, state0_15, state1_15,
        state0_16, state1_16, state0_17, state1_17, state0_18, state1_18, state0_19, state1_19,
        state0_20, state1_20, state0_21, state1_21, state0_22, state1_22, state0_23, state1_23,
        state0_24, state1_24, state0_25, state1_25, state0_26, state1_26, state0_27, state1_27,
        state0_28, state1_28, state0_29, state1_29, state0_30, state1_30, state0_31, state1_31,
        state0_32, state1_32, state0_33, state1_33, state0_34, state1_34, state0_35, state1_35,
        state0_36, state1_36, state0_37, state1_37, state0_38, state1_38, state0_39, state1_39,
        state0_40, state1_40, state0_41, state1_41, state0_42, state1_42, state0_43, state1_43,
        state0_44, state1_44 : int;
    var alpha, beta_, beta', gamma, gamma', eta_, z, v, u: FieldR.F;
    var k0, k1, k2: FieldR.F;
    var n: int;
    var l_0_at_z, l_n_minus_one_at_z: FieldR.F;
    var q_a, q_b, q_c, q_d, q_ab, q_ac, q_const, q_d_next: g;
    var sigma_0, sigma_1, sigma_2, sigma_3, lookup_selector, table_type: g;
    var custom_gate_selector: g;
    var d0, d1, t: g;
    var f_at_z, omega: FieldR.F;
    var copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient: FieldR.F;
    var col_0, col_1, col_2, col_3: g;
    var e, f: g;
    var aggregatedAtZSlot, aggregatedAtZOmegaSlot, pairing_pair_with_generator, pairing_buffer_point: g;
    var aggregatedOpeningAtZ, aggregatedOpeningAtZSlot, aggregationChallenge, firstDCoeff, firstTCoeff, copyPermutationCoeff, aggregatedOpeningAtZOmega, aggregatedValue: FieldR.F;
    var pairing_pair_with_x: g;
    isValid <- true;
    k0 <- FieldR.inF Constants.NON_RESIDUE_0;
    k1 <- FieldR.inF Constants.NON_RESIDUE_1;
    k2 <- FieldR.inF Constants.NON_RESIDUE_2;
    n <- Constants.DOMAIN_SIZE;
    q_a <- vk_gate_setup_0;
    q_b <- vk_gate_setup_1;
    q_c <- vk_gate_setup_2;
    q_d <- vk_gate_setup_3;
    q_ab <- vk_gate_setup_4;
    q_ac <- vk_gate_setup_5;
    q_const <- vk_gate_setup_6;
    q_d_next <- vk_gate_setup_7;
    custom_gate_selector <- vk_gate_selectors_1;
    sigma_0 <- vk_permutation_0;
    sigma_1 <- vk_permutation_1;
    sigma_2 <- vk_permutation_2;
    sigma_3 <- vk_permutation_3;
    lookup_selector <- vk_lookup_selector;
    table_type <- vk_lookup_table_type;
    omega <- Constants.OMEGAFr;
    col_0 <- vk_lookup_table_0;
    col_1 <- vk_lookup_table_1;
    col_2 <- vk_lookup_table_2;
    col_3 <- vk_lookup_table_3;

    (* /*////////////////////////////////////////////////////////////// *)
    (*                         1. Load Proof *)
    (* //////////////////////////////////////////////////////////////*/ *)

    (* /// @dev This function loads a zk-SNARK proof, ensures it's properly formatted, and stores it in memory. *)
    (* /// It ensures the number of inputs and the elliptic curve point's validity. *)
    (* /// Note: It does NOT reject inputs that exceed these module sizes, but rather wraps them within the *)
    (* /// module bounds. *)
    (* /// The proof consists of: *)
    (* /// 1. Public input: (1 field element from F_r) *)
    (* /// *)
    (* /// 2. Polynomial commitments (elliptic curve points over F_q): *)
    (* ///     [a], [b], [c], [d]         - state polynomials commitments *)
    (* ///     [z_perm]                   - copy-permutation grand product commitment *)
    (* ///     [s]                        - polynomial for lookup argument commitment *)
    (* ///     [z_lookup]                 - lookup grand product commitment *)
    (* ///     [t_0], [t_1], [t_2], [t_3] - quotient polynomial parts commitments *)
    (* ///     [W], [W']                  - proof openings commitments *)
    (* /// *)
    (* /// 3. Polynomial evaluations at z and z*omega (field elements from F_r): *)
    (* ///     t(z)                                  - quotient polynomial opening *)
    (* ///     a(z), b(z), c(z), d(z), d(z*omega)    - state polynomials openings *)
    (* ///     main_gate_selector(z)                 - main gate selector opening *)
    (* ///     sigma_0(z), sigma_1(z), sigma_2(z)    - permutation polynomials openings *)
    (* ///     z_perm(z*omega)                       - copy-permutation grand product opening *)
    (* ///     z_lookup(z*omega)                     - lookup grand product opening *)
    (* ///     lookup_selector(z)                    - lookup selector opening *)
    (* ///     s(x*omega), t(z*omega), table_type(z) - lookup argument polynomial openings *)
    (* ///     r(z)                                  - linearisation polynomial opening *)
    (* /// *)
    (* /// 4. Recursive proof (0 or 2 elliptic curve points over F_q) *)
    (* proof note: the inputs to this are already on the curve by typing, so only the other checks remain *)
      
    isValid <- public_input_length_in_words = 1;
    isValid <- isValid /\ (proof_length_in_words = 44);
    isValid <- isValid /\ (recursive_proof_length_in_words = 0);
    public_input <- FieldR.inF ((FieldR.asint public_input) %% 2^253);

    (* /*////////////////////////////////////////////////////////////// *)
    (*                         2. Transcript initialization             *)
    (* //////////////////////////////////////////////////////////////*/ *)

    (* /// @notice Recomputes all challenges *)
    (* /// @dev The process is the following: *)
    (* /// Commit:   PI, [a], [b], [c], [d] *)
    (* /// Get:      eta *)
    (* /// Commit:   [s] *)
    (* /// Get:      beta, gamma *)
    (* /// Commit:   [z_perm] *)
    (* /// Get:      beta', gamma' *)
    (* /// Commit:   [z_lookup] *)
    (* /// Get:      alpha *)
    (* /// Commit:   [t_0], [t_1], [t_2], [t_3] *)
    (* /// Get:      z *)
    (* /// Commit:   t(z), a(z), b(z), c(z), d(z), d(z*omega), *)
    (* ///           main_gate_selector(z), *)
    (* ///           sigma_0(z), sigma_1(z), sigma_2(z), *)
    (* ///           z_perm(z*omega), *)
    (* ///           t(z), lookup_selector(z), table_type(z), *)
    (* ///           s(x*omega), z_lookup(z*omega), t(z*omega), *)
    (* ///           r(z) *)
    (* /// Get:      v *)
    (* /// Commit:   [W], [W'] *)
    (* /// Get:      u *)  

    state <- commit_g (commit_g (commit_g (commit_g (commit_fr (0,0)
      public_input)
      a)
      b)
      c)
      d;
    eta_ <- get_commitment state 0;

    state <- commit_g state s;
    beta_ <- get_commitment state 1;
    gamma <- get_commitment state 2;

    state <- commit_g state z_perm;
    beta' <- get_commitment state 3;
    gamma' <- get_commitment state 4;

    state <- commit_g state z_lookup;
    alpha <- get_commitment state 5;

    state <- commit_g (commit_g (commit_g (commit_g state
      t_0)
      t_1)
      t_2)
      t_3;
    z <- get_commitment state 6;

    state <- commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr (commit_fr state
      quotient_poly_opening_at_z)
      a_at_z)
      b_at_z)
      c_at_z)
      d_at_z)
      d_at_z_omega)
      main_gate_selector_at_z)
      sigma_0_at_z)
      sigma_1_at_z)
      sigma_2_at_z)
      z_perm_at_z_omega)
      t_at_z)
      lookup_selector_at_z)
      table_type_at_z)
      s_at_z_omega)
      z_lookup_at_z_omega)
      t_at_z_omega)
      r_at_z;
    v <- get_commitment state 7;

    state <- commit_g (commit_g state
      w)
      w';
    u <- get_commitment state 8;

    (* /*////////////////////////////////////////////////////////////// *)
    (*                         3. Verifying quotient evaluation         *)
    (* //////////////////////////////////////////////////////////////*/ *)

    (* /// @notice Compute linearisation polynomial's constant term: r_0 *)
    (* /// @dev To save a verifier scalar multiplication, we split linearisation polynomial *)
    (* /// into its constant and non-constant terms. The constant term is computed with the formula: *)
    (* /// *)
    (* /// r_0 = alpha^0 * L_0(z) * PI * q_{main selector}(z) + r(z)         -- main gate contribution *)
    (* /// *)
    (* ///     - alpha^4 * z_perm(z*omega)(sigma_0(z) * beta + gamma + a(z)) \ *)
    (* ///                           (sigma_1(z) * beta + gamma + b(z))      | *)
    (* ///                           (sigma_2(z) * beta + gamma + c(z))      | - permutation contribution *)
    (* ///                           (sigma_3(z) + gamma)                    | *)
    (* ///     - alpha^5 * L_0(z)                                            / *)
    (* /// *)
    (* ///     + alpha^6 * (s(z*omega) * beta' + gamma' (beta' + 1))         \ *)
    (* ///               * (z - omega^{n-1}) * z_lookup(z*omega)             | - lookup contribution *)
    (* ///     - alpha^7 * L_0(z)                                            | *)
    (* ///     - alpha^8 * L_{n-1}(z) * (gamma' (beta' + 1))^{n-1}           / *)
    (* /// *)
    (* /// In the end we should check that t(z)*Z_H(z) = r(z) + r_0! *)

    isValid <- isValid /\ (z^Constants.DOMAIN_SIZE <> FieldR.one);
    l_0_at_z <- (z^Constants.DOMAIN_SIZE - FieldR.one) * ((Constants.DOMAIN_SIZEFr * (z - FieldR.one)) ^ (- 1));
    l_n_minus_one_at_z <- (Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1) * (z^Constants.DOMAIN_SIZE - FieldR.one)) * ((Constants.DOMAIN_SIZEFr * (z - Constants.OMEGAFr^(Constants.DOMAIN_SIZE- 1))) ^ (- 1));

    isValid <- isValid /\ ((quotient_poly_opening_at_z * (z^Constants.DOMAIN_SIZE - FieldR.one)) 
      = (r_at_z + l_0_at_z * public_input * main_gate_selector_at_z - alpha^4 * z_perm_at_z_omega 
      * (sigma_0_at_z * beta_ + gamma + a_at_z) 
      * (sigma_1_at_z * beta_ + gamma + b_at_z) 
      * (sigma_2_at_z * beta_ + gamma + c_at_z) 
      * (d_at_z + gamma)
      -alpha^5 * l_0_at_z  +
      ((alpha^6 * (s_at_z_omega * beta' + gamma' * (beta' + FieldR.one))
                * (z - Constants.OMEGAFr ^(Constants.DOMAIN_SIZE - 1)) * z_lookup_at_z_omega)
      - alpha^7 * l_0_at_z 
      - alpha^8 * l_n_minus_one_at_z * (gamma' * (beta' + FieldR.one)) ^ (Constants.DOMAIN_SIZE - 1))));

    (* /*////////////////////////////////////////////////////////////// *)
    (*                        4. Prepare queries                        *)
    (* //////////////////////////////////////////////////////////////*/ *)

    (* /// @dev Here we compute the first and second parts of batched polynomial commitment *)
    (* /// We use the formula: *)
    (* ///     [D0] = [t_0] + z^n * [t_1] + z^{2n} * [t_2] + z^{3n} * [t_3] *)
    (* /// and *)
    (* ///     [D1] = main_gate_selector(z) * (                                        \ *)
    (* ///                a(z) * [q_a] + b(z) * [q_b] + c(z) * [q_c] + d(z) * [q_d] +  | - main gate contribution *)
    (* ///                a(z) * b(z) * [q_ab] + a(z) * c(z) * [q_ac] +                | *)
    (* ///                [q_const] + d(z*omega) * [q_{d_next}])                       / *)
    (* /// *)
    (* ///            + alpha * [custom_gate_selector] * (                             \ *)
    (* ///                (a(z)^2 - b(z))              +                               | - custom gate contribution *)
    (* ///                (b(z)^2 - c(z))    * alpha   +                               | *)
    (* ///                (a(z)*c(z) - d(z)) * alpha^2 )                               / *)
    (* /// *)
    (* ///            + alpha^4 * [z_perm] *                                           \ *)
    (* ///                (a(z) + beta * z      + gamma) *                             | *)
    (* ///                (b(z) + beta * z * k0 + gamma) *                             | *)
    (* ///                (c(z) + beta * z * k1 + gamma) *                             | *)
    (* ///                (d(z) + beta * z * k2 + gamma)                               | - permutation contribution *)
    (* ///            - alpha^4 * z_perm(z*omega) * beta * [sigma_3] *                 | *)
    (* ///                (a(z) + beta * sigma_0(z) + gamma) *                         | *)
    (* ///                (b(z) + beta * sigma_1(z) + gamma) *                         | *)
    (* ///                (c(z) + beta * sigma_2(z) + gamma) *                         | *)
    (* ///            + alpha^5 * L_0(z) * [z_perm]                                    / *)
    (* /// *)
    (* ///            - alpha^6 * (1 + beta') * (gamma' + f(z)) * (z - omega^{n-1}) *  \ *)
    (* ///                (gamma'(1 + beta') + t(z) + beta' * t(z*omega)) * [z_lookup] | *)
    (* ///            + alpha^6 * z_lookup(z*omega) * (z - omega^{n-1}) * [s]          | - lookup contribution *)
    (* ///            + alpha^7 * L_0(z) * [z_lookup]                                  | *)
    (* ///            + alpha^8 * L_{n-1}(z) * [z_lookup]                              / *)
     
    d0 <- t_0 +           (* [D0] = [t_0] + *)
      ((z^n) * t_1) +     (*   z^n * [t_1] + *)
      ((z^(2*n)) * t_2) + (*   z^2n * [t_2] + *)
      ((z^(3*n)) * t_3);  (*   z^3n * [t_3] *)

    f_at_z <- lookup_selector_at_z * (a_at_z + eta_ * b_at_z + eta_^2 * c_at_z + eta_^3 * table_type_at_z);

    d1 <- main_gate_selector_at_z * (
        (a_at_z * q_a) +
        (b_at_z * q_b) +
        (c_at_z * q_c) +
        (d_at_z * q_d) +
        (a_at_z * b_at_z * q_ab) +
        (a_at_z * c_at_z * q_ac) +
        q_const +
        (d_at_z_omega * q_d_next)
      ) 
      + alpha * (
        (
          (a_at_z^2 - b_at_z) +
          (b_at_z^2 - c_at_z) * alpha +
          (a_at_z * c_at_z - d_at_z) * alpha^2
        )
      )* custom_gate_selector (*REVIEW: do we add a reversed G.( * ) so we can swap this round to match the comment exactly? *)
      + alpha^4 *
        (a_at_z + beta_ * z      + gamma) *                               
        (b_at_z + beta_ * z * k0 + gamma) * 
        (c_at_z + beta_ * z * k1 + gamma) * 
        (d_at_z + beta_ * z * k2 + gamma) * z_perm
      + G.inv (alpha^4 * z_perm_at_z_omega * beta_ *
        (a_at_z + beta_ * sigma_0_at_z + gamma) *
        (b_at_z + beta_ * sigma_1_at_z + gamma) *
        (c_at_z + beta_ * sigma_2_at_z + gamma) *
        sigma_3)
      + alpha^5 * l_0_at_z * z_perm
      + G.inv (alpha^6 * (FieldR.one + beta') * (gamma' + f_at_z) * (z - omega^(n-1)) *
        (gamma'*(FieldR.one + beta') + t_at_z + beta' * t_at_z_omega) * z_lookup
      ) 
      + alpha^6 * z_lookup_at_z_omega * (z - omega^(n-1)) * s
      + alpha^7 * l_0_at_z * z_lookup
      + alpha^8 * l_n_minus_one_at_z * z_lookup; 

      t <- col_0 +
        eta_ * col_1 +
        eta_^2 * col_2 +
        eta_^3 * col_3;

    (* /*////////////////////////////////////////////////////////////// *)
    (*                 5. Prepare aggregated commitment                 *)
    (* //////////////////////////////////////////////////////////////*/ *)
    (* /// @dev Here we compute aggregated commitment for the final pairing *)
    (* /// We use the formula: *)
    (* /// [E] = ( t(z) + v * r(z) *)
    (* ///       + v^2*a(z) + v^3*b(z) + v^4*c(z) + v^5*d(z) *)
    (* ///       + v^6*main_gate_selector(z) *)
    (* ///       + v^7*sigma_0(z) + v^8*sigma_1(z) + v^9*sigma_2(z) *)
    (* ///       + v^10*t(z) + v^11*lookup_selector(z) + v^12*table_type(z) *)
    (* ///       + u * (v^13*z_perm(z*omega) + v^14*d(z*omega) *)
    (* ///           + v^15*s(z*omega) + v^16*z_lookup(z*omega) + v^17*t(z*omega) *)
    (* ///       ) *)
    (* ///  ) * [1] *)
    (* /// and *)
    (* /// [F] = [D0] + v * [D1] *)
    (* ///       + v^2*[a] + v^3*[b] + v^4*[c] + v^5*[d] *)
    (* ///       + v^6*[main_gate_selector] *)
    (* ///       + v^7*[sigma_0] + v^8*[sigma_1] + v^9*[sigma_2] *)
    (* ///       + v^10*[t] + v^11*[lookup_selector] + v^12*[table_type] *)
    (* ///       + u * ( v^13*[z_perm] + v^14*[d] *)
    (* ///           + v^15*[s] + v^16*[z_lookup] + v^17*[t] *)
    (* ///       ) *)

    e <- (quotient_poly_opening_at_z (*t(z)*) + v * r_at_z
      + (v^2)*a_at_z + (v^3)+b_at_z + (v^4)*c_at_z + (v^5)*d_at_z
      + (v^6)*main_gate_selector_at_z
      + (v^7)*sigma_0_at_z + (v^8)*sigma_1_at_z + (v^9)*sigma_2_at_z
      + (v^10)*t_at_z + (v^11)*lookup_selector_at_z * (v^12)*table_type_at_z
      + u * ((v^13)*z_perm_at_z_omega + (v^14)*d_at_z_omega
        + (v^15)*s_at_z_omega + (v^16)*z_lookup_at_z_omega + (v^17)*t_at_z_omega
      )
    )* EllipticCurve.g_gen;
      
    f <- d0 + v * d1
      + (v^2)*a + (v^3)*b + (v^4)*c + (v^5)*d
      + (v^6)*vk_permutation_0
      + (v^7)*sigma_0 + (v^8)*sigma_1 + (v^9)*sigma_2
      + (v^10)*t + (v^11)*lookup_selector + (v^12)*table_type
      + u * ((v^13)*z_perm + (v^14)*d
        + (v^15)*s + (v^16)*z_lookup + (v^17)*t
      );

    (* /*////////////////////////////////////////////////////////////// *)
    (*                             5. Pairing                           *)
    (* //////////////////////////////////////////////////////////////*/ *)

    (* /// @notice Checks the final pairing *)
    (* /// @dev We should check the equation: *)
    (* /// e([W] + u * [W'], [x]_2) = e(z * [W] + u * z * omega * [W'] + [F] - [E], [1]_2), *)
    (* /// where [F] and [E] were computed previously *)
    (* /// *)
    (* /// Also we need to check that e([P1], [x]_2) = e([P2], [1]_2) *)
    (* /// if we have the recursive part of the proof *)
    (* /// where [P1] and [P2] are parts of the recursive proof *)
    (* /// *)
    (* /// We can aggregate both pairings into one for gas optimization: *)
    (* /// e([W] + u * [W'] + u^2 * [P1], [x]_2) = *)
    (* /// e(z * [W] + u * z * omega * [W'] + [F] - [E] + u^2 * [P2], [1]_2) *)
    (* /// *)
    (* /// u is a valid challenge for such aggregation, *)
    (* /// because [P1] and [P2] are used in PI *)
      
    (* TODO *)
    pairing_pair_with_generator <- e + (G.inv e);
    pairing_pair_with_generator <- (u * z * omega * w')
      + (z * w)
      + pairing_pair_with_generator;
    pairing_pair_with_x <- G.inv(w + (u * w'));

    return isValid /\ (e (pairing_pair_with_generator + pairing_pair_with_x) (Constants.G2_ELEMENT_0_G + Constants.G2_ELEMENT_1_G) = G.e);
  }

  proc high_with_spec (public_input_length_in_words: int, public_input: FieldR.F, proof_length_in_words: int, state_poly_0: g, state_poly_1: g, state_poly_2: g, state_poly_3: g, copy_permutation_grand_product: g, lookup_s_poly: g, lookup_grand_product: g, quotient_poly_part_0: g, quotient_poly_part_1: g, quotient_poly_part_2: g, quotient_poly_part_3: g, state_poly_0_opening_at_z: FieldR.F, state_poly_1_opening_at_z: FieldR.F, state_poly_2_opening_at_z: FieldR.F, state_poly_3_opening_at_z: FieldR.F, state_poly_3_opening_at_z_omega: FieldR.F, gate_selector_0_opening_at_z: FieldR.F, copy_permutation_poly_0_opening_at_z: FieldR.F, copy_permutation_poly_1_opening_at_z: FieldR.F, copy_permutation_poly_2_opening_at_z: FieldR.F, copy_permutation_grand_product_opening_at_z_omega: FieldR.F, lookup_s_poly_opening_at_z_omega: FieldR.F, lookup_grand_product_opening_at_z_omega: FieldR.F, lookup_t_poly_opening_at_z: FieldR.F, lookup_t_poly_opening_at_z_omega: FieldR.F, lookup_selector_poly_opening_at_z: FieldR.F, lookup_table_type_poly_opening_at_z: FieldR.F, quotient_poly_opening_at_z: FieldR.F, linearisation_poly_opening_at_z: FieldR.F, opening_proof_at_z: g, opening_proof_at_z_omega: g, recursive_proof_length_in_words: int, recursive_part_p1: g, recursive_part_p2: g) : bool = {
    
      (* load proof mod *)
      var _public_input, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, 
      _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, 
      _copy_permutation_grand_product_opening_at_z_omega, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, 
      _lookup_t_poly_opening_at_z, _lookup_t_poly_opening_at_z_omega, _lookup_selector_poly_opening_at_z, _lookup_table_type_poly_opening_at_z, 
      _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z : FieldR.F; 
      var _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, _quotient_poly_part_0, 
      _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _opening_proof_at_z, _opening_proof_at_z_omega: g;
      var _recursive_part_p1, _recursive_part_p2: g option;

      (* initialize transcript *)
      var state_alpha, state_beta, state_gamma, state_eta;
      var state_beta_lookup, state_gamma_lookup; 
      var state_z, state_z_in_domain, state_v, state_u;

      var state0_0, state1_0, state0_1, state1_1, state0_2, state1_2, state0_3, state1_3,
      state0_4, state1_4, state0_5, state1_5, state0_6, state1_6, state0_7, state1_7,
      state0_8, state1_8, state0_9, state1_9, state0_10, state1_10, state0_11, state1_11,
      state0_12, state1_12, state0_13, state1_13, state0_14, state1_14, state0_15, state1_15,
      state0_16, state1_16, state0_17, state1_17, state0_18, state1_18, state0_19, state1_19,
      state0_20, state1_20, state0_21, state1_21, state0_22, state1_22, state0_23, state1_23,
      state0_24, state1_24, state0_25, state1_25, state0_26, state1_26, state0_27, state1_27,
      state0_28, state1_28, state0_29, state1_29, state0_30, state1_30, state0_31, state1_31,
      state0_32, state1_32, state0_33, state1_33, state0_34, state1_34, state0_35, state1_35,
      state0_36, state1_36, state0_37, state1_37, state0_38, state1_38, state0_39, state1_39,
      state0_40, state1_40, state0_41, state1_41, state0_42, state1_42, state0_43, state1_43,
      state0_44, state1_44 : int;
    
      (* verify quotient evaluation *)
      var alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8;
      var l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega;

      (* prepare queries *)
      var query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment,
      lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated;

      (* prepare aggregated commitment *)
      var aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, aggregatedOpeningAtZOmega, pairingPairWithGeneratorSlot, pairingBufferPointSlot;

      var failed;
      failed <- false;

      (* /*////////////////////////////////////////////////////////////// *)
      (*                         1. Load Proof *)
      (* //////////////////////////////////////////////////////////////*/ *)

      (* /// @dev This function loads a zk-SNARK proof, ensures it's properly formatted, and stores it in memory. *)
      (* /// It ensures the number of inputs and the elliptic curve point's validity. *)
      (* /// Note: It does NOT reject inputs that exceed these module sizes, but rather wraps them within the *)
      (* /// module bounds. *)
      (* /// The proof consists of: *)
      (* /// 1. Public input: (1 field element from F_r) *)
      (* /// *)
      (* /// 2. Polynomial commitments (elliptic curve points over F_q): *)
      (* ///     [a], [b], [c], [d]         - state polynomials commitments *)
      (* ///     [z_perm]                   - copy-permutation grand product commitment *)
      (* ///     [s]                        - polynomial for lookup argument commitment *)
      (* ///     [z_lookup]                 - lookup grand product commitment *)
      (* ///     [t_0], [t_1], [t_2], [t_3] - quotient polynomial parts commitments *)
      (* ///     [W], [W']                  - proof openings commitments *)
      (* /// *)
      (* /// 3. Polynomial evaluations at z and z*omega (field elements from F_r): *)
      (* ///     t(z)                                  - quotient polynomial opening *)
      (* ///     a(z), b(z), c(z), d(z), d(z*omega)    - state polynomials openings *)
      (* ///     main_gate_selector(z)                 - main gate selector opening *)
      (* ///     sigma_0(z), sigma_1(z), sigma_2(z)    - permutation polynomials openings *)
      (* ///     z_perm(z*omega)                       - copy-permutation grand product opening *)
      (* ///     z_lookup(z*omega)                     - lookup grand product opening *)
      (* ///     lookup_selector(z)                    - lookup selector opening *)
      (* ///     s(x*omega), t(z*omega), table_type(z) - lookup argument polynomial openings *)
      (* ///     r(z)                                  - linearisation polynomial opening *)
      (* /// *)
      (* /// 4. Recursive proof (0 or 2 elliptic curve points over F_q) *)

      if ((public_input_length_in_words = 1) /\ (proof_length_in_words = 44) /\ (recursive_proof_length_in_words = 0)) {
      (_public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product,
        _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z,
        _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z,
        _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_s_poly_opening_at_z_omega,
        _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_t_poly_opening_at_z_omega, _lookup_selector_poly_opening_at_z,
        _lookup_table_type_poly_opening_at_z, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega,
        _recursive_part_p1, _recursive_part_p2
      ) <-
      (
        FieldR.inF ((FieldR.asint public_input) %% (2^253)),
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
        None,
        None
      );
      } else {
          (_public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product,
        _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z,
        _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z,
        _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_s_poly_opening_at_z_omega,
        _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_t_poly_opening_at_z_omega, _lookup_selector_poly_opening_at_z,
        _lookup_table_type_poly_opening_at_z, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega,
        _recursive_part_p1, _recursive_part_p2
          ) <- witness;
          failed <- true;
      }

          (* /*////////////////////////////////////////////////////////////// *)
          (*                         2. Transcript initialization *)
          (* //////////////////////////////////////////////////////////////*/ *)

          (* /// @notice Recomputes all challenges *)
          (* /// @dev The process is the following: *)
          (* /// Commit:   PI, [a], [b], [c], [d] *)
          (* /// Get:      eta *)
          (* /// Commit:   [s] *)
          (* /// Get:      beta, gamma *)
          (* /// Commit:   [z_perm] *)
          (* /// Get:      beta', gamma' *)
          (* /// Commit:   [z_lookup] *)
          (* /// Get:      alpha *)
          (* /// Commit:   [t_0], [t_1], [t_2], [t_3] *)
          (* /// Get:      z *)
          (* /// Commit:   t(z), a(z), b(z), c(z), d(z), d(z*omega), *)
          (* ///           main_gate_selector(z), *)
          (* ///           sigma_0(z), sigma_1(z), sigma_2(z), *)
          (* ///           z_perm(z*omega), *)
          (* ///           t(z), lookup_selector(z), table_type(z), *)
          (* ///           s(x*omega), z_lookup(z*omega), t(z*omega), *)
          (* ///           r(z) *)
          (* /// Get:      v *)
          (* /// Commit:   [W], [W'] *)
          (* /// Get:      u *)  

          state0_0 <- keccakT 0 0 0 (FieldR.asint _public_input);
          state1_0 <- keccakT 1 0 0 (FieldR.asint _public_input);
          state0_1 <- keccakT 0 state0_0 state1_0 (F_to_int_point (aspoint_G1 _state_poly_0)).`1;
          state1_1 <- keccakT 1 state0_0 state1_0 (F_to_int_point (aspoint_G1 _state_poly_0)).`1;
          state0_2 <- keccakT 0 state0_1 state1_1 (F_to_int_point (aspoint_G1 _state_poly_0)).`2;
          state1_2 <- keccakT 1 state0_1 state1_1 (F_to_int_point (aspoint_G1 _state_poly_0)).`2;
          state0_3 <- keccakT 0 state0_2 state1_2 (F_to_int_point (aspoint_G1 _state_poly_1)).`1;
          state1_3 <- keccakT 1 state0_2 state1_2 (F_to_int_point (aspoint_G1 _state_poly_1)).`1;
          state0_4 <- keccakT 0 state0_3 state1_3 (F_to_int_point (aspoint_G1 _state_poly_1)).`2;
          state1_4 <- keccakT 1 state0_3 state1_3 (F_to_int_point (aspoint_G1 _state_poly_1)).`2;
          state0_5 <- keccakT 0 state0_4 state1_4 (F_to_int_point (aspoint_G1 _state_poly_2)).`1;
          state1_5 <- keccakT 1 state0_4 state1_4 (F_to_int_point (aspoint_G1 _state_poly_2)).`1;
          state0_6 <- keccakT 0 state0_5 state1_5 (F_to_int_point (aspoint_G1 _state_poly_2)).`2;
          state1_6 <- keccakT 1 state0_5 state1_5 (F_to_int_point (aspoint_G1 _state_poly_2)).`2;
          state0_7 <- keccakT 0 state0_6 state1_6 (F_to_int_point (aspoint_G1 _state_poly_3)).`1;
          state1_7 <- keccakT 1 state0_6 state1_6 (F_to_int_point (aspoint_G1 _state_poly_3)).`1;
          state0_8 <- keccakT 0 state0_7 state1_7 (F_to_int_point (aspoint_G1 _state_poly_3)).`2;
          state1_8 <- keccakT 1 state0_7 state1_7 (F_to_int_point (aspoint_G1 _state_poly_3)).`2;
      
          state_eta <- FieldR.inF ((keccakC 2 state0_8 state1_8 0) %% 2^253);

          state0_9 <- keccakT 0 state0_8 state1_8 (F_to_int_point (aspoint_G1 _lookup_s_poly)).`1;
          state1_9 <- keccakT 1 state0_8 state1_8 (F_to_int_point (aspoint_G1 _lookup_s_poly)).`1;
          state0_10 <- keccakT 0 state0_9 state1_9 (F_to_int_point (aspoint_G1 _copy_permutation_grand_product)).`2;
          state1_10 <- keccakT 1 state0_9 state1_9 (F_to_int_point (aspoint_G1 _copy_permutation_grand_product)).`2;
      
          state_beta  <- FieldR.inF ((keccakC 2 state0_10 state1_10 1) %% 2^253);
          state_gamma <- FieldR.inF ((keccakC 2 state0_10 state1_10 2) %% 2^253);

          state0_11 <- keccakT 0 state0_10 state1_10 (F_to_int_point (aspoint_G1 _copy_permutation_grand_product)).`1;
          state1_11 <- keccakT 1 state0_10 state1_10 (F_to_int_point (aspoint_G1 _copy_permutation_grand_product)).`1;
          state0_12 <- keccakT 0 state0_11 state1_11 (F_to_int_point (aspoint_G1 _copy_permutation_grand_product)).`2;
          state1_12 <- keccakT 1 state0_11 state1_11 (F_to_int_point (aspoint_G1 _copy_permutation_grand_product)).`2;

          state_beta_lookup  <- FieldR.inF ((keccakC 2 state0_12 state1_12 3) %% 2^253);
          state_gamma_lookup <- FieldR.inF ((keccakC 2 state0_12 state1_12 4) %% 2^253);

          state0_13 <- keccakT 0 state0_12 state1_12 (F_to_int_point (aspoint_G1 _lookup_grand_product)).`1;
          state1_13 <- keccakT 1 state0_12 state1_12 (F_to_int_point (aspoint_G1 _lookup_grand_product)).`1;
          state0_14 <- keccakT 0 state0_13 state1_13 (F_to_int_point (aspoint_G1 _lookup_grand_product)).`2;
          state1_14 <- keccakT 1 state0_13 state1_13 (F_to_int_point (aspoint_G1 _lookup_grand_product)).`2;

          state_alpha <- FieldR.inF ((keccakC 2 state0_14 state1_14 5) %% 2^253);

          state0_15 <- keccakT 0 state0_14 state1_14 (F_to_int_point (aspoint_G1 _quotient_poly_part_0)).`1;
          state1_15 <- keccakT 1 state0_14 state1_14 (F_to_int_point (aspoint_G1 _quotient_poly_part_0)).`1;
          state0_16 <- keccakT 0 state0_15 state1_15 (F_to_int_point (aspoint_G1 _quotient_poly_part_0)).`2;
          state1_16 <- keccakT 1 state0_15 state1_15 (F_to_int_point (aspoint_G1 _quotient_poly_part_0)).`2;
          state0_17 <- keccakT 0 state0_16 state1_16 (F_to_int_point (aspoint_G1 _quotient_poly_part_1)).`1;
          state1_17 <- keccakT 1 state0_16 state1_16 (F_to_int_point (aspoint_G1 _quotient_poly_part_1)).`1;
          state0_18 <- keccakT 0 state0_17 state1_17 (F_to_int_point (aspoint_G1 _quotient_poly_part_1)).`2;
          state1_18 <- keccakT 1 state0_17 state1_17 (F_to_int_point (aspoint_G1 _quotient_poly_part_1)).`2;
          state0_19 <- keccakT 0 state0_18 state1_18 (F_to_int_point (aspoint_G1 _quotient_poly_part_2)).`1;
          state1_19 <- keccakT 1 state0_18 state1_18 (F_to_int_point (aspoint_G1 _quotient_poly_part_2)).`1;
          state0_20 <- keccakT 0 state0_19 state1_19 (F_to_int_point (aspoint_G1 _quotient_poly_part_2)).`2;
          state1_20 <- keccakT 1 state0_19 state1_19 (F_to_int_point (aspoint_G1 _quotient_poly_part_2)).`2;
          state0_21 <- keccakT 0 state0_20 state1_20 (F_to_int_point (aspoint_G1 _quotient_poly_part_3)).`1;
          state1_21 <- keccakT 1 state0_20 state1_20 (F_to_int_point (aspoint_G1 _quotient_poly_part_3)).`1;
          state0_22 <- keccakT 0 state0_21 state1_21 (F_to_int_point (aspoint_G1 _quotient_poly_part_3)).`2;
          state1_22 <- keccakT 1 state0_21 state1_21 (F_to_int_point (aspoint_G1 _quotient_poly_part_3)).`2;

          state_z <- FieldR.inF ((keccakC 2 state0_22 state1_22 6) %% 2^253);
          state_z_in_domain <- state_z^Constants.DOMAIN_SIZE;

          state0_23 <- keccakT 0 state0_22 state1_22 (FieldR.asint _quotient_poly_opening_at_z);
          state1_23 <- keccakT 1 state0_22 state1_22 (FieldR.asint _quotient_poly_opening_at_z);
          state0_24 <- keccakT 0 state0_23 state1_23 (FieldR.asint _state_poly_0_opening_at_z);
          state1_24 <- keccakT 1 state0_23 state1_23 (FieldR.asint _state_poly_0_opening_at_z);
          state0_25 <- keccakT 0 state0_24 state1_24 (FieldR.asint _state_poly_1_opening_at_z);
          state1_25 <- keccakT 1 state0_24 state1_24 (FieldR.asint _state_poly_1_opening_at_z);
          state0_26 <- keccakT 0 state0_25 state1_25 (FieldR.asint _state_poly_2_opening_at_z);
          state1_26 <- keccakT 1 state0_25 state1_25 (FieldR.asint _state_poly_2_opening_at_z);
          state0_27 <- keccakT 0 state0_26 state1_26 (FieldR.asint _state_poly_3_opening_at_z);
          state1_27 <- keccakT 1 state0_26 state1_26 (FieldR.asint _state_poly_3_opening_at_z);
          state0_28 <- keccakT 0 state0_27 state1_27 (FieldR.asint _state_poly_3_opening_at_z_omega);
          state1_28 <- keccakT 1 state0_27 state1_27 (FieldR.asint _state_poly_3_opening_at_z_omega);
          state0_29 <- keccakT 0 state0_28 state1_28 (FieldR.asint _gate_selector_0_opening_at_z);
          state1_29 <- keccakT 1 state0_28 state1_28 (FieldR.asint _gate_selector_0_opening_at_z);
          state0_30 <- keccakT 0 state0_29 state1_29 (FieldR.asint _copy_permutation_poly_0_opening_at_z);
          state1_30 <- keccakT 1 state0_29 state1_29 (FieldR.asint _copy_permutation_poly_0_opening_at_z);
          state0_31 <- keccakT 0 state0_30 state1_30 (FieldR.asint _copy_permutation_poly_1_opening_at_z);
          state1_31 <- keccakT 1 state0_30 state1_30 (FieldR.asint _copy_permutation_poly_1_opening_at_z);
          state0_32 <- keccakT 0 state0_31 state1_31 (FieldR.asint _copy_permutation_poly_2_opening_at_z);
          state1_32 <- keccakT 1 state0_31 state1_31 (FieldR.asint _copy_permutation_poly_2_opening_at_z);
          state0_33 <- keccakT 0 state0_32 state1_32 (FieldR.asint _copy_permutation_grand_product_opening_at_z_omega);
          state1_33 <- keccakT 1 state0_32 state1_32 (FieldR.asint _copy_permutation_grand_product_opening_at_z_omega);
          state0_34 <- keccakT 0 state0_33 state1_33 (FieldR.asint _lookup_t_poly_opening_at_z);
          state1_34 <- keccakT 1 state0_33 state1_33 (FieldR.asint _lookup_t_poly_opening_at_z);
          state0_35 <- keccakT 0 state0_34 state1_34 (FieldR.asint _lookup_selector_poly_opening_at_z);
          state1_35 <- keccakT 1 state0_34 state1_34 (FieldR.asint _lookup_selector_poly_opening_at_z);
          state0_36 <- keccakT 0 state0_35 state1_35 (FieldR.asint _lookup_table_type_poly_opening_at_z);
          state1_36 <- keccakT 1 state0_35 state1_35 (FieldR.asint _lookup_table_type_poly_opening_at_z);
          state0_37 <- keccakT 0 state0_36 state1_36 (FieldR.asint _lookup_s_poly_opening_at_z_omega);
          state1_37 <- keccakT 1 state0_36 state1_36 (FieldR.asint _lookup_s_poly_opening_at_z_omega);
          state0_38 <- keccakT 0 state0_37 state1_37 (FieldR.asint _lookup_grand_product_opening_at_z_omega);
          state1_38 <- keccakT 1 state0_37 state1_37 (FieldR.asint _lookup_grand_product_opening_at_z_omega);
          state0_39 <- keccakT 0 state0_38 state1_38 (FieldR.asint _lookup_t_poly_opening_at_z_omega);
          state1_39 <- keccakT 1 state0_38 state1_38 (FieldR.asint _lookup_t_poly_opening_at_z_omega);
          state0_40 <- keccakT 0 state0_39 state1_39 (FieldR.asint _linearisation_poly_opening_at_z);
          state1_40 <- keccakT 1 state0_39 state1_39 (FieldR.asint _linearisation_poly_opening_at_z);

          state_v <- FieldR.inF ((keccakC 2 state0_40 state1_40 7) %% 2^253);

          state0_41 <- keccakT 0 state0_40 state1_40 (F_to_int_point (aspoint_G1 _opening_proof_at_z)).`1;
          state1_41 <- keccakT 1 state0_40 state1_40 (F_to_int_point (aspoint_G1 _opening_proof_at_z)).`1;
          state0_42 <- keccakT 0 state0_41 state1_41 (F_to_int_point (aspoint_G1 _opening_proof_at_z)).`2;
          state1_42 <- keccakT 1 state0_41 state1_41 (F_to_int_point (aspoint_G1 _opening_proof_at_z)).`2;
          state0_43 <- keccakT 0 state0_42 state1_42 (F_to_int_point (aspoint_G1 _opening_proof_at_z_omega)).`1;
          state1_43 <- keccakT 1 state0_42 state1_42 (F_to_int_point (aspoint_G1 _opening_proof_at_z_omega)).`1;
          state0_44 <- keccakT 0 state0_43 state1_43 (F_to_int_point (aspoint_G1 _opening_proof_at_z_omega)).`2;
          state1_44 <- keccakT 1 state0_43 state1_43 (F_to_int_point (aspoint_G1 _opening_proof_at_z_omega)).`2;

          state_u <- FieldR.inF ((keccakC 2 state0_44 state1_44 8) %% 2^253);

          (* /*////////////////////////////////////////////////////////////// *)
          (*                         3. Verifying quotient evaluation *)
          (* //////////////////////////////////////////////////////////////*/ *)

          (* /// @notice Compute linearisation polynomial's constant term: r_0 *)
          (* /// @dev To save a verifier scalar multiplication, we split linearisation polynomial *)
          (* /// into its constant and non-constant terms. The constant term is computed with the formula: *)
          (* /// *)
          (* /// r_0 = alpha^0 * L_0(z) * PI * q_{main selector}(z) + r(z)         -- main gate contribution *)
          (* /// *)
          (* ///     - alpha^4 * z_perm(z*omega)(sigma_0(z) * beta + gamma + a(z)) \ *)
          (* ///                           (sigma_1(z) * beta + gamma + b(z))      | *)
          (* ///                           (sigma_2(z) * beta + gamma + c(z))      | - permutation contribution *)
          (* ///                           (sigma_3(z) + gamma)                    | *)
          (* ///     - alpha^5 * L_0(z)                                            / *)
          (* /// *)
          (* ///     + alpha^6 * (s(z*omega) * beta' + gamma' (beta' + 1))         \ *)
          (* ///               * (z - omega^{n-1}) * z_lookup(z*omega)             | - lookup contribution *)
          (* ///     - alpha^7 * L_0(z)                                            | *)
          (* ///     - alpha^8 * L_{n-1}(z) * (gamma' (beta' + 1))^{n-1}           / *)
          (* /// *)
          (* /// In the end we should check that t(z)*Z_H(z) = r(z) + r_0! *)

          if (state_z^Constants.DOMAIN_SIZE = FieldR.one) {
              failed <- true;
          } else {
              l0_at_z <- (state_z^Constants.DOMAIN_SIZE - FieldR.one) * ((Constants.DOMAIN_SIZEFr * (state_z - FieldR.one)) ^ (- 1));
              ln_minus_one_at_z <- (Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1) * (state_z^Constants.DOMAIN_SIZE - FieldR.one)) * ((Constants.DOMAIN_SIZEFr * (state_z - Constants.OMEGAFr^(Constants.DOMAIN_SIZE- 1))) ^ (- 1)); 

              failed <- failed \/ !((_quotient_poly_opening_at_z * (state_z_in_domain - FieldR.one)) 
              = (_linearisation_poly_opening_at_z + l0_at_z * _public_input * _gate_selector_0_opening_at_z -state_alpha^4 * _copy_permutation_grand_product_opening_at_z_omega
                * (_copy_permutation_poly_0_opening_at_z * state_beta + state_gamma + _state_poly_0_opening_at_z) 
                * (_copy_permutation_poly_1_opening_at_z * state_beta + state_gamma + _state_poly_1_opening_at_z) 
                * (_copy_permutation_poly_2_opening_at_z * state_beta + state_gamma + _state_poly_2_opening_at_z) 
                * (_state_poly_3_opening_at_z + state_gamma)
                -state_alpha^5 * l0_at_z  + ((state_alpha^6 * (_lookup_s_poly_opening_at_z_omega * state_beta_lookup + state_gamma_lookup * (state_beta_lookup + FieldR.one)) * _lookup_grand_product_opening_at_z_omega) * (state_z - Constants.OMEGAFr ^(Constants.DOMAIN_SIZE - 1)) 
                - state_alpha^7 * l0_at_z 
                - state_alpha^8 * ln_minus_one_at_z * (state_gamma_lookup * (state_beta_lookup + FieldR.one)) ^ (Constants.DOMAIN_SIZE - 1))));
          }
      
          (alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega) <-
          (
            state_alpha^2,
            state_alpha^3,
            state_alpha^4,
            state_alpha^5,
            state_alpha^6, 
            state_alpha^7,
            state_alpha^8,
            state_beta_lookup + FieldR.one,
            state_gamma_lookup * state_beta_lookup + state_gamma_lookup,
            state_z - Constants.OMEGAFr ^(Constants.DOMAIN_SIZE - 1)
          );

              (* /*////////////////////////////////////////////////////////////// *)
              (* 4. Prepare queries *)
              (* //////////////////////////////////////////////////////////////*/ *)

              (* /// @dev Here we compute the first and second parts of batched polynomial commitment *)
              (* /// We use the formula: *)
              (* ///     [D0] = [t_0] + z^n * [t_1] + z^{2n} * [t_2] + z^{3n} * [t_3] *)
              (* /// and *)
              (* ///     [D1] = main_gate_selector(z) * (                                        \ *)
              (* ///                a(z) * [q_a] + b(z) * [q_b] + c(z) * [q_c] + d(z) * [q_d] +  | - main gate contribution *)
              (* ///                a(z) * b(z) * [q_ab] + a(z) * c(z) * [q_ac] +                | *)
              (* ///                [q_const] + d(z*omega) * [q_{d_next}])                       / *)
              (* /// *)
              (* ///            + alpha * [custom_gate_selector] * (                             \ *)
              (* ///                (a(z)^2 - b(z))              +                               | - custom gate contribution *)
              (* ///                (b(z)^2 - c(z))    * alpha   +                               | *)
              (* ///                (a(z)*c(z) - d(z)) * alpha^2 )                               / *)
              (* /// *)
              (* ///            + alpha^4 * [z_perm] *                                           \ *)
              (* ///                (a(z) + beta * z      + gamma) *                             | *)
              (* ///                (b(z) + beta * z * k0 + gamma) *                             | *)
              (* ///                (c(z) + beta * z * k1 + gamma) *                             | *)
              (* ///                (d(z) + beta * z * k2 + gamma)                               | - permutation contribution *)
              (* ///            - alpha^4 * z_perm(z*omega) * beta * [sigma_3] *                 | *)
              (* ///                (a(z) + beta * sigma_0(z) + gamma) *                         | *)
              (* ///                (b(z) + beta * sigma_1(z) + gamma) *                         | *)
              (* ///                (c(z) + beta * sigma_2(z) + gamma) *                         | *)
              (* ///            + alpha^5 * L_0(z) * [z_perm]                                    / *)
              (* /// *)
              (* ///            - alpha^6 * (1 + beta') * (gamma' + f(z)) * (z - omega^{n-1}) *  \ *)
              (* ///                (gamma'(1 + beta') + t(z) + beta' * t(z*omega)) * [z_lookup] | *)
              (* ///            + alpha^6 * z_lookup(z*omega) * (z - omega^{n-1}) * [s]          | - lookup contribution *)
              (* ///            + alpha^7 * L_0(z) * [z_lookup]                                  | *)
              (* ///            + alpha^8 * L_{n-1}(z) * [z_lookup]                              / *)

              query_at_z_0 <- 
              _quotient_poly_part_0 +
          (state_z_in_domain * _quotient_poly_part_1) +
          ((state_z_in_domain * state_z_in_domain) * _quotient_poly_part_2) +
          ((state_z_in_domain * state_z_in_domain * state_z_in_domain) * _quotient_poly_part_3);

          
            copy_permutation_first_aggregated_commitment_coeff <- (
            alpha4 * (state_z * state_beta + state_gamma + _state_poly_0_opening_at_z) *
            (state_z * state_beta * (FieldR.inF Constants.NON_RESIDUE_0) + state_gamma + _state_poly_1_opening_at_z) *
            (state_z * state_beta * (FieldR.inF Constants.NON_RESIDUE_1) + state_gamma + _state_poly_2_opening_at_z) *
            (state_z * state_beta * (FieldR.inF Constants.NON_RESIDUE_2) + state_gamma + _state_poly_3_opening_at_z) +
              l0_at_z * alpha5
          ) * state_v;


              query_at_z_1 <- (((
                ((_state_poly_0_opening_at_z * _state_poly_0_opening_at_z - _state_poly_1_opening_at_z) * state_alpha) +
                ((_state_poly_1_opening_at_z * _state_poly_1_opening_at_z - _state_poly_2_opening_at_z) * alpha2) +
                ((_state_poly_2_opening_at_z * _state_poly_0_opening_at_z - _state_poly_3_opening_at_z) * alpha3)
              ) * state_v) * vk_gate_selectors_1) + ((state_v * _gate_selector_0_opening_at_z) * (
              (_state_poly_0_opening_at_z * vk_gate_setup_0) +
              (_state_poly_1_opening_at_z * vk_gate_setup_1) +
              (_state_poly_2_opening_at_z * vk_gate_setup_2) +
              (_state_poly_3_opening_at_z * vk_gate_setup_3) +
              ((_state_poly_0_opening_at_z * _state_poly_1_opening_at_z) * vk_gate_setup_4) +
              ((_state_poly_0_opening_at_z * _state_poly_2_opening_at_z) * vk_gate_setup_5) +
                vk_gate_setup_6 +
              (state_poly_3_opening_at_z_omega * vk_gate_setup_7)
            )) + (G.inv ((
                alpha4 * state_beta * _copy_permutation_grand_product_opening_at_z_omega *
                (_copy_permutation_poly_0_opening_at_z * state_beta + state_gamma + _state_poly_0_opening_at_z) *
                (_copy_permutation_poly_1_opening_at_z * state_beta + state_gamma + _state_poly_1_opening_at_z) *
                (_copy_permutation_poly_2_opening_at_z * state_beta + state_gamma + _state_poly_2_opening_at_z) *
                  state_v
              ) * vk_permutation_3));


                  lookupSFirstAggregatedCommitment <- state_v * z_minus_last_omega * alpha6 * _lookup_grand_product_opening_at_z_omega;
                  lookupGrandProductFirstAggregatedCoefficient 
                  <- ((- (_lookup_t_poly_opening_at_z_omega * state_beta_lookup +
                  _lookup_t_poly_opening_at_z + beta_gamma_plus_gamma) *
              ((_state_poly_0_opening_at_z + state_eta * _state_poly_1_opening_at_z +
                state_eta * state_eta * _state_poly_2_opening_at_z +
                state_eta * state_eta * state_eta * _lookup_table_type_poly_opening_at_z) *
                _lookup_selector_poly_opening_at_z + state_gamma_lookup)) *
                beta_plus_one * alpha6 * z_minus_last_omega + alpha7 * l0_at_z +
                alpha8 * ln_minus_one_at_z) *
                state_v;
          

                query_t_poly_aggregated <-
                vk_lookup_table_0 +
          (state_eta * vk_lookup_table_1) +
          (state_eta * state_eta) * vk_lookup_table_2 +
          (state_eta * state_eta * state_eta) * vk_lookup_table_3;

            (* /*////////////////////////////////////////////////////////////// *)
            (* 5. Prepare aggregated commitment *)
            (* //////////////////////////////////////////////////////////////*/ *)

            (* /// @dev Here we compute aggregated commitment for the final pairing *)
            (* /// We use the formula: *)
            (* /// [E] = ( t(z) + v * r(z) *)
            (* ///       + v^2*a(z) + v^3*b(z) + v^4*c(z) + v^5*d(z) *)
            (* ///       + v^6*main_gate_selector(z) *)
            (* ///       + v^7*sigma_0(z) + v^8*sigma_1(z) + v^9*sigma_2(z) *)
            (* ///       + v^10*t(z) + v^11*lookup_selector(z) + v^12*table_type(z) *)
            (* ///       + u * (v^13*z_perm(z*omega) + v^14*d(z*omega) *)
            (* ///           + v^15*s(z*omega) + v^16*z_lookup(z*omega) + v^17*t(z*omega) *)
            (* ///       ) *)
            (* ///  ) * [1] *)
            (* /// and *)
            (* /// [F] = [D0] + v * [D1] *)
            (* ///       + v^2*[a] + v^3*[b] + v^4*[c] + v^5*[d] *)
            (* ///       + v^6*[main_gate_selector] *)
            (* ///       + v^7*[sigma_0] + v^8*[sigma_1] + v^9*[sigma_2] *)
            (* ///       + v^10*[t] + v^11*[lookup_selector] + v^12*[table_type] *)
            (* ///       + u * ( v^13*[z_perm] + v^14*[d] *)
            (* ///           + v^15*[s] + v^16*[z_lookup] + v^17*[t] *)
            (* ///       ) *)

            (* t(z) + v * r(z) + v^2*a(z) + v^3*b(z) + v^4*c(z) + v^6*main_gate_selector(z) + v^7*sigma_0(z) + v^8*sigma_1(z) + v^9*sigma_2(z) + v^11*lookup_selector(z) + v^12*table_type(z) *)

            (* // v^5*d(z) + v^10*t(z) *)
            aggregatedAtZSlot <- query_at_z_0 + query_at_z_1 + state_v ^ 2 * _state_poly_0 + state_v ^ 3 * _state_poly_1 + state_v ^ 4 * _state_poly_2 (* term "state_v ^ 5 * _state_poly_3" from aggregatedAtZOmegaSlot *) + state_v ^ 6 * vk_gate_selectors_0 + state_v ^ 7 * vk_permutation_0 + state_v ^ 8 * vk_permutation_1 + state_v ^ 9 * vk_permutation_2 (* term "state_v ^ 10 * query_t_poly_aggregated" from aggregatedAtZOmegaSlot *) + state_v ^ 11 * vk_lookup_selector + state_v ^ 12 * vk_lookup_table_type;

            aggregatedOpeningAtZSlot <- _quotient_poly_opening_at_z + state_v * _linearisation_poly_opening_at_z + state_v ^ 2 * _state_poly_0_opening_at_z + state_v ^ 3 * _state_poly_1_opening_at_z + state_v ^ 4 * _state_poly_2_opening_at_z + state_v ^ 5 * _state_poly_3_opening_at_z + state_v ^ 6 * _gate_selector_0_opening_at_z + state_v ^ 7 * _copy_permutation_poly_0_opening_at_z + state_v ^ 8 * _copy_permutation_poly_1_opening_at_z + state_v ^ 9 * _copy_permutation_poly_2_opening_at_z + state_v ^ 10 * _lookup_t_poly_opening_at_z + state_v ^ 11 * _lookup_selector_poly_opening_at_z + state_v ^ 12 * _lookup_table_type_poly_opening_at_z; (* + state_v ^ 12 * _lookup_table_type_poly_opening_at_z ??? *)


            (* u * ( v^13*[z_perm] + v^14*[d] + v^15*[s] + v^16*[z_lookup] + v^17*[t]) + v^5*d(z) + v^10*t(z) *)
            (* + lookupGrandProductFirstAggregatedCoefficient * _lookup_grand_product + lookupSFirstAggregatedCommitment * _lookup_s_poly + copy_permutation_first_aggregated_commitment_coeff * _copy_permutation_grand_product ????? *) 
            aggregatedAtZOmegaSlot <- state_u * (
            state_v ^ 13 * _copy_permutation_grand_product + state_v ^ 14 * _state_poly_3 + state_v ^ 15 * _lookup_s_poly + state_v ^ 16 * _lookup_grand_product + state_v ^ 17 * query_t_poly_aggregated
          ) + state_v ^ 10 * query_t_poly_aggregated + state_v ^ 5 * _state_poly_3
            + lookupGrandProductFirstAggregatedCoefficient * _lookup_grand_product (* [z_lookup] *) + lookupSFirstAggregatedCommitment * _lookup_s_poly (* [s] *) + copy_permutation_first_aggregated_commitment_coeff * _copy_permutation_grand_product (* [z_prem] *);
          (* *) 
          

            (* v^13*[z_perm] + v^14*[d] + v^15*[s] + v^16*[z_lookup] + v^17*[t] *)
            aggregatedOpeningAtZOmega <- state_v ^ 13 * _copy_permutation_grand_product_opening_at_z_omega + state_v ^ 14 * _state_poly_3_opening_at_z_omega + state_v ^ 15 * _lookup_s_poly_opening_at_z_omega + state_v ^ 16 * _lookup_grand_product_opening_at_z_omega + state_v ^ 17 * _lookup_t_poly_opening_at_z_omega; 

            pairingPairWithGeneratorSlot <- aggregatedAtZSlot + aggregatedAtZOmegaSlot; (* [F] *)
          
            pairingBufferPointSlot <- (aggregatedOpeningAtZOmega * state_u + _quotient_poly_opening_at_z + state_v * _linearisation_poly_opening_at_z + state_v ^ 2 * _state_poly_0_opening_at_z + state_v ^ 3 * _state_poly_1_opening_at_z + state_v ^ 4 * _state_poly_2_opening_at_z + state_v ^ 5 * _state_poly_3_opening_at_z + state_v ^ 6 * _gate_selector_0_opening_at_z + state_v ^ 7 * _copy_permutation_poly_0_opening_at_z + state_v ^ 8 * _copy_permutation_poly_1_opening_at_z + state_v ^ 9 * _copy_permutation_poly_2_opening_at_z + state_v ^ 10 * _lookup_t_poly_opening_at_z + state_v ^ 11 * _lookup_selector_poly_opening_at_z + state_v ^ 12 * _lookup_table_type_poly_opening_at_z) * EllipticCurve.g_gen; (* [E] *)

            (* /*////////////////////////////////////////////////////////////// *)
            (*                         5. Pairing *)
            (* //////////////////////////////////////////////////////////////*/ *)

            (* /// @notice Checks the final pairing *)
            (* /// @dev We should check the equation: *)
            (* /// e([W] + u * [W'], [x]_2) = e(z * [W] + u * z * omega * [W'] + [F] - [E], [1]_2), *)
            (* /// where [F] and [E] were computed previously *)
            (* /// *)
            (* /// Also we need to check that e([P1], [x]_2) = e([P2], [1]_2) *)
            (* /// if we have the recursive part of the proof *)
            (* /// where [P1] and [P2] are parts of the recursive proof *)
            (* /// *)
            (* /// We can aggregate both pairings into one for gas optimization: *)
            (* /// e([W] + u * [W'] + u^2 * [P1], [x]_2) = *)
            (* /// e(z * [W] + u * z * omega * [W'] + [F] - [E] + u^2 * [P2], [1]_2) *)
            (* /// *)
            (* /// u is a valid challenge for such aggregation, *)
            (* /// because [P1] and [P2] are used in PI *)

            pairingPairWithGeneratorSlot <- pairingPairWithGeneratorSlot + (G.inv pairingBufferPointSlot);
            pairingPairWithGeneratorSlot <- (state_z * _opening_proof_at_z) + pairingPairWithGeneratorSlot;
            pairingPairWithGeneratorSlot <- ((state_z * Constants.OMEGAFr * state_u) * _opening_proof_at_z_omega) + pairingPairWithGeneratorSlot;
            failed <- failed \/ !(e (pairingPairWithGeneratorSlot + (G.inv ((state_u * _opening_proof_at_z_omega) + _opening_proof_at_z))) (Constants.G2_ELEMENT_0_G + Constants.G2_ELEMENT_1_G) = G.e);
    
            return !failed;
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
