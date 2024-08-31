pragma Goals:printall.

require import InitializeTranscript.
require import Field.
require import FinalPairing.
require import LoadProof.
require import LoadVerificationKey.
require import PrepareAggregatedCommitment.
require import PrepareQueries.
require import UInt256.
require import Utils.
require import Verifier.
require import VerifyQuotientEvaluation.
require import YulPrimops.

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
   var query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment,
       lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated;

   (* prepare aggregated commitment *)
   var prepare_aggregated_commitment_opt;
   var aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, aggregatedOpeningAtZOmega, pairingPairWithGeneratorSlot, pairingBufferPointSlot;
   
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
    (state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_eta, state_z, state_z_in_domain, state_v, state_u) <@ InitializeTranscript.mid(0, 0, _public_input, _state_poly_0.`1, _state_poly_0.`2, _state_poly_1.`1, _state_poly_1.`2, _state_poly_2.`1, _state_poly_2.`2, _state_poly_3.`1, _state_poly_3.`2, _lookup_s_poly.`1, _lookup_s_poly.`2, _copy_permutation_grand_product.`1, _copy_permutation_grand_product.`2, _lookup_grand_product.`1, _lookup_grand_product.`2, _quotient_poly_part_0.`1, _quotient_poly_part_0.`2, _quotient_poly_part_1.`1, _quotient_poly_part_1.`2, _quotient_poly_part_2.`1, _quotient_poly_part_2.`2, _quotient_poly_part_3.`1, _quotient_poly_part_3.`2, _quotient_poly_opening_at_z, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_selector_poly_opening_at_z, _lookup_table_type_poly_opening_at_z, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z_omega, _linearisation_poly_opening_at_z, _opening_proof_at_z.`1, _opening_proof_at_z.`2, _opening_proof_at_z_omega.`1, _opening_proof_at_z_omega.`2);
    
    (verify_quotient_evaluation_opt, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega) <@ VerifyQuotientEvaluation.mid(state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_z, _public_input, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _gate_selector_0_opening_at_z, _linearisation_poly_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, state_z_in_domain, _quotient_poly_opening_at_z);
    failed <- failed \/ !(odflt false verify_quotient_evaluation_opt);

    prepare_queries_opt <@ PrepareQueries.mid(state_z_in_domain, _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, (vk_lookup_table_0X, vk_lookup_table_0Y), (vk_lookup_table_1X, vk_lookup_table_1Y), (vk_lookup_table_2X, vk_lookup_table_2Y), (vk_lookup_table_3X, vk_lookup_table_3Y), state_eta, (vk_gate_setup_0X, vk_gate_setup_0Y), (vk_gate_setup_1X, vk_gate_setup_1Y), (vk_gate_setup_2X, vk_gate_setup_2Y), (vk_gate_setup_3X, vk_gate_setup_3Y), (vk_gate_setup_4X, vk_gate_setup_4Y), (vk_gate_setup_5X, vk_gate_setup_5Y), (vk_gate_setup_6X, vk_gate_setup_6Y), (vk_gate_setup_7X, vk_gate_setup_7Y), _state_poly_3_opening_at_z_omega, state_v, state_z, _gate_selector_0_opening_at_z, state_alpha, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, state_beta, state_gamma, (vk_gate_selectors_1X, vk_gate_selectors_1Y), (vk_permutation_3X, vk_permutation_3Y), _copy_permutation_grand_product_opening_at_z_omega, l0_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _lookup_grand_product_opening_at_z_omega, z_minus_last_omega, _lookup_t_poly_opening_at_z_omega, state_beta_lookup, _lookup_t_poly_opening_at_z, beta_gamma_plus_gamma, _lookup_table_type_poly_opening_at_z, _lookup_selector_poly_opening_at_z, state_gamma_lookup, beta_plus_one, ln_minus_one_at_z);
    failed <- failed \/ is_none prepare_queries_opt;
    (query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated) <- oget prepare_queries_opt;

    prepare_aggregated_commitment_opt <@ PrepareAggregatedCommitment.mid(query_at_z_0, _quotient_poly_opening_at_z, query_at_z_1, state_v, _linearisation_poly_opening_at_z, _state_poly_0, _state_poly_0_opening_at_z, _state_poly_1, _state_poly_1_opening_at_z, _state_poly_2, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, (vk_gate_selectors_0X, vk_gate_selectors_0Y), _gate_selector_0_opening_at_z, (vk_permutation_0X, vk_permutation_0Y), _copy_permutation_poly_0_opening_at_z, (vk_permutation_1X, vk_permutation_1Y), _copy_permutation_poly_1_opening_at_z, (vk_permutation_2X, vk_permutation_2Y), _copy_permutation_poly_2_opening_at_z, _lookup_t_poly_opening_at_z, (vk_lookup_selector_X, vk_lookup_selector_Y), _lookup_selector_poly_opening_at_z, (vk_lookup_table_type_X, vk_lookup_table_type_Y), _lookup_table_type_poly_opening_at_z, copy_permutation_first_aggregated_commitment_coeff, state_u, _copy_permutation_grand_product, _copy_permutation_grand_product_opening_at_z_omega, _state_poly_3, _state_poly_3_opening_at_z_omega, _lookup_s_poly, _lookup_s_poly_opening_at_z_omega, lookupSFirstAggregatedCommitment, _lookup_grand_product, _lookup_grand_product_opening_at_z_omega, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated, _lookup_t_poly_opening_at_z_omega);
   failed <- failed \/ is_none prepare_aggregated_commitment_opt;
   (aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, aggregatedOpeningAtZOmega, pairingPairWithGeneratorSlot, pairingBufferPointSlot) <- oget prepare_aggregated_commitment_opt;

  final_pairing_bool <@ FinalPairing.mid(state_u, state_z, pairingPairWithGeneratorSlot, pairingBufferPointSlot, _opening_proof_at_z, _opening_proof_at_z_omega, vk_recursive_flag, recursive_part_p1, recursive_part_p2);
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

    (aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, aggregatedOpeningAtZOmega, pairingPairWithGeneratorSlot, pairingBufferPointSlot) <@ PrepareAggregatedCommitment.high_encapsulated(query_at_z_0, _quotient_poly_opening_at_z, query_at_z_1, state_v, _linearisation_poly_opening_at_z, _state_poly_0, _state_poly_0_opening_at_z, _state_poly_1, _state_poly_1_opening_at_z, _state_poly_2, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, vk_gate_selectors_0, _gate_selector_0_opening_at_z, vk_permutation_0, _copy_permutation_poly_0_opening_at_z, vk_permutation_1, _copy_permutation_poly_1_opening_at_z, vk_permutation_2, _copy_permutation_poly_2_opening_at_z, _lookup_t_poly_opening_at_z, vk_lookup_selector, _lookup_selector_poly_opening_at_z, vk_lookup_table_type, _lookup_table_type_poly_opening_at_z, copy_permutation_first_aggregated_commitment_coeff, state_u, _copy_permutation_grand_product, _copy_permutation_grand_product_opening_at_z_omega, _state_poly_3, _state_poly_3_opening_at_z_omega, _lookup_s_poly, _lookup_s_poly_opening_at_z_omega, lookupSFirstAggregatedCommitment, _lookup_grand_product, _lookup_grand_product_opening_at_z_omega, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated, _lookup_t_poly_opening_at_z_omega);

  final_pairing_bool <@ FinalPairing.high(state_u, state_z, pairingPairWithGeneratorSlot, pairingBufferPointSlot, _opening_proof_at_z, _opening_proof_at_z_omega, vk_recursive_flag, recursive_part_p1, recursive_part_p2);
  failed <- failed \/ !final_pairing_bool;
   
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

import MemoryMap VerifierConsts ConcretePrimops PurePrimops.

op verify_memory_footprint (m: mem) =
let m1 = loadVerificationKey_memory_footprint m in
m1.

(* lemma verify_low_equiv_mid (memory : mem):
equiv [
    Verify.low ~ Verify.mid :
      !Primops.reverted{1} /\ 
      Primops.memory{1} = memory /\
      (* load proof from calldata *)
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
      recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
      recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2
      ==>
      !Primops.reverted{1} /\
      Primops.memory{1} = loadVerificationKey_memory_footprint memory
    ].
proof. proc. progress.    
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
W256.to_uint (load mlvk VK_GATE_SETUP_0_X_SLOT) = vk_gate_setup_0X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_0_Y_SLOT) = vk_gate_setup_0Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_1_X_SLOT) = vk_gate_setup_1X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_1_Y_SLOT) = vk_gate_setup_1Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_2_X_SLOT) = vk_gate_setup_2X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_2_Y_SLOT) = vk_gate_setup_2Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_3_X_SLOT) = vk_gate_setup_3X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_3_Y_SLOT) = vk_gate_setup_3Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_4_X_SLOT) = vk_gate_setup_4X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_4_Y_SLOT) = vk_gate_setup_4Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_5_X_SLOT) = vk_gate_setup_5X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_5_Y_SLOT) = vk_gate_setup_5Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_6_X_SLOT) = vk_gate_setup_6X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_6_Y_SLOT) = vk_gate_setup_6Y{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_7_X_SLOT) = vk_gate_setup_7X{2} /\
W256.to_uint (load mlvk VK_GATE_SETUP_7_Y_SLOT) = vk_gate_setup_7Y{2} /\
W256.to_uint (load mlvk VK_GATE_SELECTORS_0_X_SLOT) = vk_gate_selectors_0X{2} /\ 
W256.to_uint (load mlvk VK_GATE_SELECTORS_0_Y_SLOT) = vk_gate_selectors_0Y{2} /\
W256.to_uint (load mlvk VK_GATE_SELECTORS_1_X_SLOT) = vk_gate_selectors_1X{2} /\
W256.to_uint (load mlvk VK_GATE_SELECTORS_1_Y_SLOT) = vk_gate_selectors_1Y{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_0_X_SLOT) = vk_permutation_0X{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_0_Y_SLOT) = vk_permutation_0Y{2} /\   
W256.to_uint (load mlvk VK_PERMUTATION_1_X_SLOT) = vk_permutation_1X{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_1_Y_SLOT) = vk_permutation_1Y{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_2_X_SLOT) = vk_permutation_2X{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_2_Y_SLOT) = vk_permutation_2Y{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_3_X_SLOT) = vk_permutation_3X{2} /\
W256.to_uint (load mlvk VK_PERMUTATION_3_Y_SLOT) = vk_permutation_3Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_0_X_SLOT) = vk_lookup_table_0X{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_0_Y_SLOT) = vk_lookup_table_0Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_1_X_SLOT) = vk_lookup_table_1X{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_1_Y_SLOT) = vk_lookup_table_1Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_2_X_SLOT) = vk_lookup_table_2X{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_2_Y_SLOT) = vk_lookup_table_2Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_3_X_SLOT) = vk_lookup_table_3X{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_3_Y_SLOT) = vk_lookup_table_3Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_SELECTOR_X_SLOT) = vk_lookup_selector_X{2} /\
W256.to_uint (load mlvk VK_LOOKUP_SELECTOR_Y_SLOT) = vk_lookup_selector_Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_TYPE_X_SLOT) = vk_lookup_table_type_X{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) = vk_lookup_table_type_Y{2} /\
W256.to_uint (load mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) = vk_lookup_table_type_Y{2} /\
load mlvk VK_RECURSIVE_FLAG_SLOT = uint256_of_bool vk_recursive_flag{2}).
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
clear m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 
      m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 m38 m39 m40 m41.
*)

lemma verify_mid_equiv_high_encapsulated:
    equiv [
      Verify.mid ~ Verify.high_encapsulated:
        ={public_input_length_in_words} /\
        public_input{1} = FieldR.asint public_input{2} /\
        ={proof_length_in_words} /\
        state_poly_0{1} = F_to_int_point(aspoint_G1 state_poly_0{2}) /\
        state_poly_1{1} = F_to_int_point(aspoint_G1 state_poly_1{2}) /\
        state_poly_2{1} = F_to_int_point(aspoint_G1 state_poly_2{2}) /\
        state_poly_3{1} = F_to_int_point(aspoint_G1 state_poly_3{2}) /\
        copy_permutation_grand_product{1} = F_to_int_point(aspoint_G1 copy_permutation_grand_product{2}) /\
        lookup_s_poly{1} = F_to_int_point(aspoint_G1 lookup_s_poly{2}) /\
        lookup_grand_product{1} = F_to_int_point(aspoint_G1 lookup_grand_product{2}) /\
        quotient_poly_part_0{1} = F_to_int_point(aspoint_G1 quotient_poly_part_0{2}) /\
        quotient_poly_part_1{1} = F_to_int_point(aspoint_G1 quotient_poly_part_1{2}) /\
        quotient_poly_part_2{1} = F_to_int_point(aspoint_G1 quotient_poly_part_2{2}) /\
        quotient_poly_part_3{1} = F_to_int_point(aspoint_G1 quotient_poly_part_3{2}) /\
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
        opening_proof_at_z{1} = F_to_int_point(aspoint_G1 opening_proof_at_z{2}) /\
        opening_proof_at_z_omega{1} = F_to_int_point(aspoint_G1 opening_proof_at_z_omega{2}) /\
        ={recursive_proof_length_in_words} /\
        recursive_part_p1{1} = F_to_int_point(aspoint_G1 recursive_part_p1{2}) /\
        recursive_part_p2{1} = F_to_int_point(aspoint_G1 recursive_part_p2{2}) ==> 
        ={res}
    ].
    proof.
      proc.
      simplify.
      sp.
      seq 3 3: (
        (failed{1} /\ failed{2}) \/
        (!failed{1} /\ !failed{2} /\
        _public_input{1} = FieldR.asint _public_input{2} /\
        _state_poly_0{1} = F_to_int_point(aspoint_G1 _state_poly_0{2}) /\
        _state_poly_1{1} = F_to_int_point(aspoint_G1 _state_poly_1{2}) /\
        _state_poly_2{1} = F_to_int_point(aspoint_G1 _state_poly_2{2}) /\
        _state_poly_3{1} = F_to_int_point(aspoint_G1 _state_poly_3{2}) /\
        _copy_permutation_grand_product{1} = F_to_int_point(aspoint_G1 _copy_permutation_grand_product{2}) /\
        _lookup_s_poly{1} = F_to_int_point(aspoint_G1 _lookup_s_poly{2}) /\
        _lookup_grand_product{1} = F_to_int_point(aspoint_G1 _lookup_grand_product{2}) /\
        _quotient_poly_part_0{1} = F_to_int_point(aspoint_G1 _quotient_poly_part_0{2}) /\
        _quotient_poly_part_1{1} = F_to_int_point(aspoint_G1 _quotient_poly_part_1{2}) /\
        _quotient_poly_part_2{1} = F_to_int_point(aspoint_G1 _quotient_poly_part_2{2}) /\
        _quotient_poly_part_3{1} = F_to_int_point(aspoint_G1 _quotient_poly_part_3{2}) /\
        _state_poly_0_opening_at_z{1} = FieldR.asint _state_poly_0_opening_at_z{2} /\
        _state_poly_1_opening_at_z{1} = FieldR.asint _state_poly_1_opening_at_z{2} /\
        _state_poly_2_opening_at_z{1} = FieldR.asint _state_poly_2_opening_at_z{2} /\
        _state_poly_3_opening_at_z{1} = FieldR.asint _state_poly_3_opening_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = FieldR.asint _state_poly_3_opening_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = FieldR.asint _gate_selector_0_opening_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = FieldR.asint _copy_permutation_poly_0_opening_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = FieldR.asint _copy_permutation_poly_1_opening_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = FieldR.asint _copy_permutation_poly_2_opening_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = FieldR.asint _copy_permutation_grand_product_opening_at_z_omega{2} /\
        _lookup_s_poly_opening_at_z_omega{1} = FieldR.asint _lookup_s_poly_opening_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = FieldR.asint _lookup_grand_product_opening_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = FieldR.asint _lookup_t_poly_opening_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = FieldR.asint _lookup_t_poly_opening_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = FieldR.asint _lookup_selector_poly_opening_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = FieldR.asint _lookup_table_type_poly_opening_at_z{2} /\
        _quotient_poly_opening_at_z{1} = FieldR.asint _quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = FieldR.asint _linearisation_poly_opening_at_z{2} /\
        _opening_proof_at_z{1} = F_to_int_point(aspoint_G1 _opening_proof_at_z{2}) /\
        _opening_proof_at_z_omega{1} = F_to_int_point(aspoint_G1 _opening_proof_at_z_omega{2}) /\
        _recursive_part_p1{1} = (omap F_to_int_point (omap aspoint_G1 _recursive_part_p1{2})) /\
        _recursive_part_p2{1} = (omap F_to_int_point (omap aspoint_G1 _recursive_part_p2{2}))
      )).
      wp.
      call (loadProof_mid_equiv_high false). skip.
      progress.
      case H. by progress. by progress.

      seq 1 1: (
        (failed{1} /\ failed{2}) \/ (
          !failed{1} /\  !failed{2} /\
          _public_input{1} = FieldR.asint _public_input{2} /\
          _state_poly_0{1} = F_to_int_point (aspoint_G1 _state_poly_0{2}) /\
          _state_poly_1{1} = F_to_int_point (aspoint_G1 _state_poly_1{2}) /\
           _state_poly_2{1} = F_to_int_point (aspoint_G1 _state_poly_2{2}) /\
          _state_poly_3{1} = F_to_int_point (aspoint_G1 _state_poly_3{2}) /\
          _copy_permutation_grand_product{1} = F_to_int_point (aspoint_G1 _copy_permutation_grand_product{2}) /\
          _lookup_s_poly{1} = F_to_int_point (aspoint_G1 _lookup_s_poly{2}) /\
          _lookup_grand_product{1} = F_to_int_point (aspoint_G1 _lookup_grand_product{2}) /\
          _quotient_poly_part_0{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_0{2}) /\
          _quotient_poly_part_1{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_1{2}) /\
          _quotient_poly_part_2{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_2{2}) /\
          _quotient_poly_part_3{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_3{2}) /\
          _state_poly_0_opening_at_z{1} = FieldR.asint _state_poly_0_opening_at_z{2} /\
          _state_poly_1_opening_at_z{1} = FieldR.asint _state_poly_1_opening_at_z{2} /\
          _state_poly_2_opening_at_z{1} = FieldR.asint _state_poly_2_opening_at_z{2} /\
          _state_poly_3_opening_at_z{1} = FieldR.asint _state_poly_3_opening_at_z{2} /\
          _state_poly_3_opening_at_z_omega{1} = FieldR.asint _state_poly_3_opening_at_z_omega{2} /\
          _gate_selector_0_opening_at_z{1} = FieldR.asint _gate_selector_0_opening_at_z{2} /\
          _copy_permutation_poly_0_opening_at_z{1} = FieldR.asint _copy_permutation_poly_0_opening_at_z{2} /\
          _copy_permutation_poly_1_opening_at_z{1} = FieldR.asint _copy_permutation_poly_1_opening_at_z{2} /\
          _copy_permutation_poly_2_opening_at_z{1} = FieldR.asint _copy_permutation_poly_2_opening_at_z{2} /\
          _copy_permutation_grand_product_opening_at_z_omega{1} = FieldR.asint _copy_permutation_grand_product_opening_at_z_omega{2} /\
          _lookup_s_poly_opening_at_z_omega{1} = FieldR.asint _lookup_s_poly_opening_at_z_omega{2} /\
          _lookup_grand_product_opening_at_z_omega{1} = FieldR.asint _lookup_grand_product_opening_at_z_omega{2} /\
          _lookup_t_poly_opening_at_z_omega{1} = FieldR.asint _lookup_t_poly_opening_at_z_omega{2} /\
          _lookup_selector_poly_opening_at_z{1} = FieldR.asint _lookup_selector_poly_opening_at_z{2} /\
           _lookup_table_type_poly_opening_at_z{1} = FieldR.asint _lookup_table_type_poly_opening_at_z{2} /\
          _quotient_poly_opening_at_z{1} = FieldR.asint _quotient_poly_opening_at_z{2} /\
          _linearisation_poly_opening_at_z{1} = FieldR.asint _linearisation_poly_opening_at_z{2} /\
          _opening_proof_at_z{1} = F_to_int_point (aspoint_G1 _opening_proof_at_z{2}) /\
          _opening_proof_at_z_omega{1} = F_to_int_point (aspoint_G1 _opening_proof_at_z_omega{2}) /\
          _recursive_part_p1{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p1{2}) /\
          _recursive_part_p2{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p2{2}) /\
          state_alpha{1} = FieldR.asint state_alpha{2} /\
          state_beta{1} = FieldR.asint state_beta{2} /\
          state_beta_lookup{1} = FieldR.asint state_beta_lookup{2} /\
          state_gamma{1} = FieldR.asint state_gamma{2} /\
          state_gamma_lookup{1} = FieldR.asint state_gamma_lookup{2} /\
          state_eta{1} = FieldR.asint state_eta{2} /\
          state_z{1} = FieldR.asint state_z{2} /\
          state_z_in_domain{1} = FieldR.asint state_z_in_domain{2} /\
          state_v{1} = FieldR.asint state_v{2} /\
          state_u{1} = FieldR.asint state_u{2}
        )
      ).
      case (failed{1}).
      conseq (_: failed{1} /\ failed{2} ==> failed{1} /\ failed{2}).
      progress. case H. by progress. by progress.
      progress. left. rewrite H1 H2. by progress.
      kill{1} 1. inline*. wp. skip. by progress.
      kill{2} 1. inline*. wp. skip. by progress.
      skip. by progress.
      exists* _public_input{2}, _state_poly_0{2}, _state_poly_1{2}, _state_poly_2{2}, _state_poly_3{2}, _lookup_s_poly{2}, _copy_permutation_grand_product{2}, _lookup_grand_product{2}, _quotient_poly_part_0{2}, _quotient_poly_part_1{2}, _quotient_poly_part_2{2}, _quotient_poly_part_3{2}, _quotient_poly_opening_at_z{2}, _state_poly_0_opening_at_z{2}, _state_poly_1_opening_at_z{2}, _state_poly_2_opening_at_z{2}, _state_poly_3_opening_at_z{2}, _state_poly_3_opening_at_z_omega{2}, _gate_selector_0_opening_at_z{2}, _copy_permutation_poly_0_opening_at_z{2}, _copy_permutation_poly_1_opening_at_z{2}, _copy_permutation_poly_2_opening_at_z{2}, _copy_permutation_grand_product_opening_at_z_omega{2}, _lookup_t_poly_opening_at_z{2}, _lookup_selector_poly_opening_at_z{2}, _lookup_table_type_poly_opening_at_z{2}, _lookup_s_poly_opening_at_z_omega{2}, _lookup_grand_product_opening_at_z_omega{2}, _lookup_t_poly_opening_at_z_omega{2}, _linearisation_poly_opening_at_z{2}, _opening_proof_at_z{2}, _opening_proof_at_z_omega{2}.
      elim* => _public_input_r _state_poly_0_r _state_poly_1_r _state_poly_2_r _state_poly_3_r _lookup_s_poly_r _copy_permutation_grand_product_r _lookup_grand_product_r _quotient_poly_part_0_r _quotient_poly_part_1_r _quotient_poly_part_2_r _quotient_poly_part_3_r _quotient_poly_opening_at_z_r _state_poly_0_opening_at_z_r _state_poly_1_opening_at_z_r _state_poly_2_opening_at_z_r _state_poly_3_opening_at_z_r _state_poly_3_opening_at_z_omega_r _gate_selector_0_opening_at_z_r _copy_permutation_poly_0_opening_at_z_r _copy_permutation_poly_1_opening_at_z_r _copy_permutation_poly_2_opening_at_z_r _copy_permutation_grand_product_opening_at_z_omega_r _lookup_t_poly_opening_at_z_r _lookup_selector_poly_opening_at_z_r _lookup_table_type_poly_opening_at_z_r _lookup_s_poly_opening_at_z_omega_r _lookup_grand_product_opening_at_z_omega_r _lookup_t_poly_opening_at_z_omega_r _linearisation_poly_opening_at_z_r _opening_proof_at_z_r _opening_proof_at_z_omega_r.
      call (initializeTranscript_mid_equiv_high 0 0 _public_input_r _state_poly_0_r _state_poly_1_r _state_poly_2_r _state_poly_3_r _lookup_s_poly_r _copy_permutation_grand_product_r _lookup_grand_product_r _quotient_poly_part_0_r _quotient_poly_part_1_r _quotient_poly_part_2_r _quotient_poly_part_3_r _quotient_poly_opening_at_z_r _state_poly_0_opening_at_z_r _state_poly_1_opening_at_z_r _state_poly_2_opening_at_z_r _state_poly_3_opening_at_z_r _state_poly_3_opening_at_z_omega_r _gate_selector_0_opening_at_z_r _copy_permutation_poly_0_opening_at_z_r _copy_permutation_poly_1_opening_at_z_r _copy_permutation_poly_2_opening_at_z_r _copy_permutation_grand_product_opening_at_z_omega_r _lookup_t_poly_opening_at_z_r _lookup_selector_poly_opening_at_z_r _lookup_table_type_poly_opening_at_z_r _lookup_s_poly_opening_at_z_omega_r _lookup_grand_product_opening_at_z_omega_r _lookup_t_poly_opening_at_z_omega_r _linearisation_poly_opening_at_z_r _opening_proof_at_z_r _opening_proof_at_z_omega_r).
      wp. skip. progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. progress. rewrite H H55. progress.
      admit.
      (* rewrite -H27 FieldR.inFK -Constants.r_eq_fieldr_p /Constants.R pmod_small. smt (). reflexivity.
      rewrite -H30 FieldR.inFK -Constants.r_eq_fieldr_p /Constants.R pmod_small. smt (). reflexivity.
      rewrite -H33 FieldR.inFK -Constants.r_eq_fieldr_p /Constants.R pmod_small. smt (). reflexivity.
      rewrite -H36 FieldR.inFK -Constants.r_eq_fieldr_p /Constants.R pmod_small. smt (). reflexivity.
      rewrite -H39 FieldR.inFK -Constants.r_eq_fieldr_p /Constants.R pmod_small. smt (). reflexivity.
      rewrite -H42 FieldR.inFK -Constants.r_eq_fieldr_p /Constants.R pmod_small. smt (). reflexivity.
      rewrite -H45 FieldR.inFK -Constants.r_eq_fieldr_p /Constants.R pmod_small. smt (). reflexivity.
      rewrite -H48 FieldR.inFK -Constants.r_eq_fieldr_p /Constants.R pmod_small. smt (). reflexivity.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      admit. *)
      qed.