pragma Goals:printall.

require import AllCore.
require import Int.
require import IntDiv.

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
require import PurePrimops.
require import Utils.

lemma initializeTranscript_low_pspec_revert:
phoare [ InitializeTranscript.low : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. admit. qed.

lemma verifyQuotientEvaluation_low_pspec_revert:
phoare [ VerifyQuotientEvaluation.low : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. admit. qed.

import MemoryMap VerifierConsts.

lemma loadProof_low_equiv_mid_mod (mem_0: mem) (recursive: bool):
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
       /\
       0 <= r.`1 < 2^253 /\
       0 <= r.`2.`1 < Constants.Q /\ 0 <= r.`2.`2 < Constants.Q /\
       0 <= r.`3.`1 < Constants.Q /\ 0 <= r.`3.`2 < Constants.Q /\
       0 <= r.`4.`1 < Constants.Q /\ 0 <= r.`4.`2 < Constants.Q /\
       0 <= r.`5.`1 < Constants.Q /\ 0 <= r.`5.`2 < Constants.Q /\
       0 <= r.`6.`1 < Constants.Q /\ 0 <= r.`6.`2 < Constants.Q /\
       0 <= r.`7.`1 < Constants.Q /\ 0 <= r.`7.`2 < Constants.Q /\
       0 <= r.`8.`1 < Constants.Q /\ 0 <= r.`8.`2 < Constants.Q /\
       0 <= r.`9.`1 < Constants.Q /\ 0 <= r.`9.`2 < Constants.Q /\
       0 <= r.`10.`1 < Constants.Q /\ 0 <= r.`10.`2 < Constants.Q /\
       0 <= r.`11.`1 < Constants.Q /\ 0 <= r.`11.`2 < Constants.Q /\
       0 <= r.`12.`1 < Constants.Q /\ 0 <= r.`12.`2 < Constants.Q /\
       0 <= r.`13 < Constants.R /\
       0 <= r.`14 < Constants.R /\
       0 <= r.`15 < Constants.R /\
       0 <= r.`16 < Constants.R /\
       0 <= r.`17 < Constants.R /\
       0 <= r.`18 < Constants.R /\
       0 <= r.`19 < Constants.R /\
       0 <= r.`20 < Constants.R /\
       0 <= r.`21 < Constants.R /\
       0 <= r.`22 < Constants.R /\
       0 <= r.`23 < Constants.R /\
       0 <= r.`24 < Constants.R /\
       0 <= r.`25 < Constants.R /\
       0 <= r.`26 < Constants.R /\
       0 <= r.`27 < Constants.R /\
       0 <= r.`28 < Constants.R /\
       0 <= r.`29 < Constants.R /\
       0 <= r.`30 < Constants.R /\
       0 <= r.`31.`1 < Constants.Q /\ 0 <= r.`31.`2 < Constants.Q /\
       0 <= r.`32.`1 < Constants.Q /\ 0 <= r.`32.`2 < Constants.Q
      )    
    ].
proof. admit. qed.

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
    (state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_eta, state_z, state_z_in_domain, state_v, state_u) <@ InitializeTranscript.mid(0, 0, _public_input, _state_poly_0.`1, _state_poly_0.`2, _state_poly_1.`1, _state_poly_1.`2, _state_poly_2.`1, _state_poly_2.`2, _state_poly_3.`1, _state_poly_3.`2, _lookup_s_poly.`1, _lookup_s_poly.`2, _copy_permutation_grand_product.`1, _copy_permutation_grand_product.`2, _lookup_grand_product.`1, _lookup_grand_product.`2, _quotient_poly_part_0.`1, _quotient_poly_part_0.`2, _quotient_poly_part_1.`1, _quotient_poly_part_1.`2, _quotient_poly_part_2.`1, _quotient_poly_part_2.`2, _quotient_poly_part_3.`1, _quotient_poly_part_3.`2, _quotient_poly_opening_at_z, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_selector_poly_opening_at_z, _lookup_table_type_poly_opening_at_z, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z_omega, _linearisation_poly_opening_at_z, _opening_proof_at_z.`1, _opening_proof_at_z.`2, _opening_proof_at_z_omega.`1, _opening_proof_at_z_omega.`2);
    
    (verify_quotient_evaluation_opt, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega) <@ VerifyQuotientEvaluation.mid(state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_z, _public_input, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _gate_selector_0_opening_at_z, _linearisation_poly_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, state_z_in_domain, _quotient_poly_opening_at_z);
    failed <- failed \/ !(odflt false verify_quotient_evaluation_opt);

    prepare_queries_opt <@ PrepareQueries.mid(state_z_in_domain, _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, (vk_lookup_table_0X, vk_lookup_table_0Y), (vk_lookup_table_1X, vk_lookup_table_1Y), (vk_lookup_table_2X, vk_lookup_table_2Y), (vk_lookup_table_3X, vk_lookup_table_3Y), state_eta, (vk_gate_setup_0X, vk_gate_setup_0Y), (vk_gate_setup_1X, vk_gate_setup_1Y), (vk_gate_setup_2X, vk_gate_setup_2Y), (vk_gate_setup_3X, vk_gate_setup_3Y), (vk_gate_setup_4X, vk_gate_setup_4Y), (vk_gate_setup_5X, vk_gate_setup_5Y), (vk_gate_setup_6X, vk_gate_setup_6Y), (vk_gate_setup_7X, vk_gate_setup_7Y), _state_poly_3_opening_at_z_omega, state_v, state_z, _gate_selector_0_opening_at_z, state_alpha, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, state_beta, state_gamma, (vk_gate_selectors_1X, vk_gate_selectors_1Y), (vk_permutation_3X, vk_permutation_3Y), _copy_permutation_grand_product_opening_at_z_omega, l0_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _lookup_grand_product_opening_at_z_omega, z_minus_last_omega, _lookup_t_poly_opening_at_z_omega, state_beta_lookup, _lookup_t_poly_opening_at_z, beta_gamma_plus_gamma, _lookup_table_type_poly_opening_at_z, _lookup_selector_poly_opening_at_z, state_gamma_lookup, beta_plus_one, ln_minus_one_at_z);
    failed <- failed \/ is_none prepare_queries_opt;
    (query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookup_s_first_aggregated_commitment, lookup_grand_product_first_aggregated_coefficient, query_t_poly_aggregated) <- oget prepare_queries_opt;

    prepare_aggregated_commitment_opt <@ PrepareAggregatedCommitment.mid(query_at_z_0, _quotient_poly_opening_at_z, query_at_z_1, state_v, _linearisation_poly_opening_at_z, _state_poly_0, _state_poly_0_opening_at_z, _state_poly_1, _state_poly_1_opening_at_z, _state_poly_2, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, (vk_gate_selectors_0X, vk_gate_selectors_0Y), _gate_selector_0_opening_at_z, (vk_permutation_0X, vk_permutation_0Y), _copy_permutation_poly_0_opening_at_z, (vk_permutation_1X, vk_permutation_1Y), _copy_permutation_poly_1_opening_at_z, (vk_permutation_2X, vk_permutation_2Y), _copy_permutation_poly_2_opening_at_z, _lookup_t_poly_opening_at_z, (vk_lookup_selector_X, vk_lookup_selector_Y), _lookup_selector_poly_opening_at_z, (vk_lookup_table_type_X, vk_lookup_table_type_Y), _lookup_table_type_poly_opening_at_z, copy_permutation_first_aggregated_commitment_coeff, state_u, _copy_permutation_grand_product, _copy_permutation_grand_product_opening_at_z_omega, _state_poly_3, _state_poly_3_opening_at_z_omega, _lookup_s_poly, _lookup_s_poly_opening_at_z_omega, lookup_s_first_aggregated_commitment, _lookup_grand_product, _lookup_grand_product_opening_at_z_omega, lookup_grand_product_first_aggregated_coefficient, query_t_poly_aggregated, _lookup_t_poly_opening_at_z_omega);
   failed <- failed \/ is_none prepare_aggregated_commitment_opt;
   (aggregated_at_z, aggregated_opening_at_z, aggregated_at_z_omega, aggregated_opening_at_z_omega, pairing_pair_with_generator, pairing_buffer_point) <- oget prepare_aggregated_commitment_opt;

  final_pairing_bool <@ FinalPairing.mid(state_u, state_z, pairing_pair_with_generator, pairing_buffer_point, _opening_proof_at_z, _opening_proof_at_z_omega, vk_recursive_flag, recursive_part_p1, recursive_part_p2);
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

import MemoryMap VerifierConsts PurePrimops.

op verify_memory_footprint (m: mem) =
let m1 = loadVerificationKey_memory_footprint m in
m1.

op w256_of_int_pair (a: int*int) : (uint256 * uint256) = (W256.of_int a.`1, W256.of_int a.`2).

lemma verify_low_equiv_mid (memory : mem):
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
      recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
      mload memory TRANSCRIPT_STATE_0_SLOT = W256.zero /\ (* assumption that EVM memory starts zeroed *)
      mload memory TRANSCRIPT_STATE_1_SLOT = W256.zero
      ==>
      (!Primops.reverted{1} /\ res{2} = true) \/ (Primops.reverted{1} /\ res{2} = false)
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
seq 41 42: (
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
recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
W256.to_uint (mload mlvk VK_GATE_SETUP_0_X_SLOT) = vk_gate_setup_0X{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_0_Y_SLOT) = vk_gate_setup_0Y{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_1_X_SLOT) = vk_gate_setup_1X{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_1_Y_SLOT) = vk_gate_setup_1Y{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_2_X_SLOT) = vk_gate_setup_2X{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_2_Y_SLOT) = vk_gate_setup_2Y{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_3_X_SLOT) = vk_gate_setup_3X{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_3_Y_SLOT) = vk_gate_setup_3Y{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_4_X_SLOT) = vk_gate_setup_4X{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_4_Y_SLOT) = vk_gate_setup_4Y{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_5_X_SLOT) = vk_gate_setup_5X{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_5_Y_SLOT) = vk_gate_setup_5Y{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_6_X_SLOT) = vk_gate_setup_6X{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_6_Y_SLOT) = vk_gate_setup_6Y{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_7_X_SLOT) = vk_gate_setup_7X{2} /\
W256.to_uint (mload mlvk VK_GATE_SETUP_7_Y_SLOT) = vk_gate_setup_7Y{2} /\
W256.to_uint (mload mlvk VK_GATE_SELECTORS_0_X_SLOT) = vk_gate_selectors_0X{2} /\ 
W256.to_uint (mload mlvk VK_GATE_SELECTORS_0_Y_SLOT) = vk_gate_selectors_0Y{2} /\
W256.to_uint (mload mlvk VK_GATE_SELECTORS_1_X_SLOT) = vk_gate_selectors_1X{2} /\
W256.to_uint (mload mlvk VK_GATE_SELECTORS_1_Y_SLOT) = vk_gate_selectors_1Y{2} /\
W256.to_uint (mload mlvk VK_PERMUTATION_0_X_SLOT) = vk_permutation_0X{2} /\
W256.to_uint (mload mlvk VK_PERMUTATION_0_Y_SLOT) = vk_permutation_0Y{2} /\   
W256.to_uint (mload mlvk VK_PERMUTATION_1_X_SLOT) = vk_permutation_1X{2} /\
W256.to_uint (mload mlvk VK_PERMUTATION_1_Y_SLOT) = vk_permutation_1Y{2} /\
W256.to_uint (mload mlvk VK_PERMUTATION_2_X_SLOT) = vk_permutation_2X{2} /\
W256.to_uint (mload mlvk VK_PERMUTATION_2_Y_SLOT) = vk_permutation_2Y{2} /\
W256.to_uint (mload mlvk VK_PERMUTATION_3_X_SLOT) = vk_permutation_3X{2} /\
W256.to_uint (mload mlvk VK_PERMUTATION_3_Y_SLOT) = vk_permutation_3Y{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_0_X_SLOT) = vk_lookup_table_0X{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_0_Y_SLOT) = vk_lookup_table_0Y{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_1_X_SLOT) = vk_lookup_table_1X{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_1_Y_SLOT) = vk_lookup_table_1Y{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_2_X_SLOT) = vk_lookup_table_2X{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_2_Y_SLOT) = vk_lookup_table_2Y{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_3_X_SLOT) = vk_lookup_table_3X{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_3_Y_SLOT) = vk_lookup_table_3Y{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_SELECTOR_X_SLOT) = vk_lookup_selector_X{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_SELECTOR_Y_SLOT) = vk_lookup_selector_Y{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_X_SLOT) = vk_lookup_table_type_X{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) = vk_lookup_table_type_Y{2} /\
W256.to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) = vk_lookup_table_type_Y{2} /\
mload mlvk VK_RECURSIVE_FLAG_SLOT = uint256_of_bool vk_recursive_flag{2} /\
mload mlvk TRANSCRIPT_STATE_0_SLOT = W256.zero /\
mload mlvk TRANSCRIPT_STATE_1_SLOT = W256.zero /\
vk_recursive_flag{2} = false /\
failed{2} = false /\  
!Primops.reverted{1} /\ 
Primops.memory{1} = mlvk).
wp; inline LoadVerificationKey.low;
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
/VK_RECURSIVE_FLAG_SLOT /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_STATE_1_SLOT.
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
rewrite load_store_same /uint256_of_bool; by simplify.
do 41! (rewrite load_store_diff; [by simplify | by simplify |]). by progress.
do 41! (rewrite load_store_diff; [by simplify | by simplify |]). by progress.
clear m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 
      m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 m38 m39 m40 m41.

have aux: forall n x, 0 <= x < n => n < W256.modulus => x %% W256.modulus = x.
progress. apply mod_eq_self. by simplify. by simplify. smt().

have aux_q: Constants.Q < W256.modulus. smt().
have aux_r: Constants.R < W256.modulus. smt().

exists* vk_recursive_flag{2}; elim*=> rf.
seq 1 3:(
 rf = vk_recursive_flag{2} /\ vk_recursive_flag{2} = false /\
  public_input_length_in_words{2} = to_uint load_calldata_public_input_length /\
  public_input{2} = to_uint load_calldata_public_input /\
  proof_length_in_words{2} = to_uint load_calldata_proof_length /\
  state_poly_0{2} = point_to_uint load_calldata_state_poly_0 /\
  state_poly_1{2} = point_to_uint load_calldata_state_poly_1 /\
  state_poly_2{2} = point_to_uint load_calldata_state_poly_2 /\
  state_poly_3{2} = point_to_uint load_calldata_state_poly_3 /\
  copy_permutation_grand_product{2} =
  point_to_uint load_calldata_copy_permutation_grand_product /\
  lookup_s_poly{2} = point_to_uint load_calldata_lookup_s_poly /\
  lookup_grand_product{2} = point_to_uint load_calldata_lookup_grand_product /\
  quotient_poly_part_0{2} = point_to_uint load_calldata_quotient_poly_part_0 /\
  quotient_poly_part_1{2} = point_to_uint load_calldata_quotient_poly_part_1 /\
  quotient_poly_part_2{2} = point_to_uint load_calldata_quotient_poly_part_2 /\
  quotient_poly_part_3{2} = point_to_uint load_calldata_quotient_poly_part_3 /\
  state_poly_0_opening_at_z{2} =
  to_uint load_calldata_state_poly_0_opening_at_z /\
  state_poly_1_opening_at_z{2} =
  to_uint load_calldata_state_poly_1_opening_at_z /\
  state_poly_2_opening_at_z{2} =
  to_uint load_calldata_state_poly_2_opening_at_z /\
  state_poly_3_opening_at_z{2} =
  to_uint load_calldata_state_poly_3_opening_at_z /\
  state_poly_3_opening_at_z_omega{2} =
  to_uint load_calldata_state_poly_3_opening_at_z_omega /\
  gate_selector_0_opening_at_z{2} =
  to_uint load_calldata_gate_selector_0_opening_at_z /\
  copy_permutation_poly_0_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_0_opening_at_z /\
  copy_permutation_poly_1_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_1_opening_at_z /\
  copy_permutation_poly_2_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_2_opening_at_z /\
  copy_permutation_grand_product_opening_at_z_omega{2} =
  to_uint load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
  lookup_s_poly_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_s_poly_opening_at_z_omega /\
  lookup_grand_product_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_grand_product_opening_at_z_omega /\
  lookup_t_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_t_poly_opening_at_z /\
  lookup_t_poly_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_t_poly_opening_at_z_omega /\
  lookup_selector_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_selector_poly_opening_at_z /\
  lookup_table_type_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_table_type_poly_opening_at_z /\
  quotient_poly_opening_at_z{2} =
  to_uint load_calldata_quotient_poly_opening_at_z /\
  linearisation_poly_opening_at_z{2} =
  to_uint load_calldata_linearisation_poly_opening_at_z /\
  opening_proof_at_z{2} = point_to_uint load_calldata_opening_proof_at_z /\
  opening_proof_at_z_omega{2} =
  point_to_uint load_calldata_opening_proof_at_z_omega /\
  recursive_proof_length_in_words{2} =
  to_uint load_calldata_recursive_proof_length /\
  recursive_part_p1{2} = point_to_uint load_calldata_recursive_part_p1 /\
  recursive_part_p2{2} = point_to_uint load_calldata_recursive_part_p2 /\
  to_uint (mload mlvk VK_GATE_SETUP_0_X_SLOT) = vk_gate_setup_0X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_0_Y_SLOT) = vk_gate_setup_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_X_SLOT) = vk_gate_setup_1X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_Y_SLOT) = vk_gate_setup_1Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_X_SLOT) = vk_gate_setup_2X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_Y_SLOT) = vk_gate_setup_2Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_X_SLOT) = vk_gate_setup_3X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_Y_SLOT) = vk_gate_setup_3Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_X_SLOT) = vk_gate_setup_4X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_Y_SLOT) = vk_gate_setup_4Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_X_SLOT) = vk_gate_setup_5X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_Y_SLOT) = vk_gate_setup_5Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_X_SLOT) = vk_gate_setup_6X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_Y_SLOT) = vk_gate_setup_6Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_X_SLOT) = vk_gate_setup_7X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_Y_SLOT) = vk_gate_setup_7Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_X_SLOT) = vk_gate_selectors_0X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_Y_SLOT) = vk_gate_selectors_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_X_SLOT) = vk_gate_selectors_1X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_Y_SLOT) = vk_gate_selectors_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_X_SLOT) = vk_permutation_0X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_Y_SLOT) = vk_permutation_0Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_X_SLOT) = vk_permutation_1X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_Y_SLOT) = vk_permutation_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_X_SLOT) = vk_permutation_2X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_Y_SLOT) = vk_permutation_2Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_X_SLOT) = vk_permutation_3X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_Y_SLOT) = vk_permutation_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_X_SLOT) = vk_lookup_table_0X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_Y_SLOT) = vk_lookup_table_0Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_X_SLOT) = vk_lookup_table_1X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_Y_SLOT) = vk_lookup_table_1Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_X_SLOT) = vk_lookup_table_2X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_Y_SLOT) = vk_lookup_table_2Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_X_SLOT) = vk_lookup_table_3X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_Y_SLOT) = vk_lookup_table_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_X_SLOT) = vk_lookup_selector_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_Y_SLOT) = vk_lookup_selector_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_X_SLOT) =
  vk_lookup_table_type_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) =
  vk_lookup_table_type_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) =
  vk_lookup_table_type_Y{2} /\
  mload mlvk VK_RECURSIVE_FLAG_SLOT = uint256_of_bool vk_recursive_flag{2} /\
  mload mlvk TRANSCRIPT_STATE_0_SLOT = W256.zero /\ (* assumption that EVM memory starts zeroed *)
  mload mlvk TRANSCRIPT_STATE_1_SLOT = W256.zero /\
 ((Primops.reverted{1} /\ failed{2}) \/
 (!Primops.reverted{1} /\ !failed{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_PUBLIC_INPUT) = _public_input{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_0_X_SLOT) = _state_poly_0{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_0_Y_SLOT) = _state_poly_0{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_1_X_SLOT) = _state_poly_1{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_1_Y_SLOT) = _state_poly_1{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_2_X_SLOT) = _state_poly_2{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_2_Y_SLOT) = _state_poly_2{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_3_X_SLOT) = _state_poly_3{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_3_Y_SLOT) = _state_poly_3{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_S_POLY_X_SLOT) = _lookup_s_poly{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_S_POLY_Y_SLOT) = _lookup_s_poly{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT) = _copy_permutation_grand_product{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT) = _copy_permutation_grand_product{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT) = _lookup_grand_product{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT) = _lookup_grand_product{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT) = _quotient_poly_part_0{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT) = _quotient_poly_part_0{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT) = _quotient_poly_part_1{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT) = _quotient_poly_part_1{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT) = _quotient_poly_part_2{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT) = _quotient_poly_part_2{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT) = _quotient_poly_part_3{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT) = _quotient_poly_part_3{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = _quotient_poly_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = _state_poly_0_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = _state_poly_1_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = _state_poly_2_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = _state_poly_3_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) = _state_poly_3_opening_at_z_omega{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = _gate_selector_0_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = _copy_permutation_poly_0_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = _copy_permutation_poly_1_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = _copy_permutation_poly_2_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = _copy_permutation_grand_product_opening_at_z_omega{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) = _lookup_t_poly_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) = _lookup_selector_poly_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) = _lookup_table_type_poly_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = _lookup_s_poly_opening_at_z_omega{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = _lookup_grand_product_opening_at_z_omega{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) = _lookup_t_poly_opening_at_z_omega{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = _linearisation_poly_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_X_SLOT) = _opening_proof_at_z{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_Y_SLOT) = _opening_proof_at_z{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT) = _opening_proof_at_z_omega{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT) = _opening_proof_at_z_omega{2}.`2 /\
  Primops.memory{1} = loadProof_memory_footprint
   mlvk vk_recursive_flag{2} (W256.of_int _public_input{2}) (point_of_uint _state_poly_0{2}) (point_of_uint _state_poly_1{2}) (point_of_uint _state_poly_2{2}) (point_of_uint _state_poly_3{2})
   (point_of_uint _copy_permutation_grand_product{2}) (point_of_uint _lookup_s_poly{2}) (point_of_uint _lookup_grand_product{2}) (point_of_uint _quotient_poly_part_0{2})
   (point_of_uint _quotient_poly_part_1{2}) (point_of_uint _quotient_poly_part_2{2}) (point_of_uint _quotient_poly_part_3{2}) (W256.of_int _state_poly_0_opening_at_z{2})
   (W256.of_int _state_poly_1_opening_at_z{2}) (W256.of_int _state_poly_2_opening_at_z{2}) (W256.of_int _state_poly_3_opening_at_z{2}) (W256.of_int _state_poly_3_opening_at_z_omega{2})
   (W256.of_int _gate_selector_0_opening_at_z{2}) (W256.of_int _copy_permutation_poly_0_opening_at_z{2}) (W256.of_int _copy_permutation_poly_1_opening_at_z{2})
   (W256.of_int _copy_permutation_poly_2_opening_at_z{2}) (W256.of_int _copy_permutation_grand_product_opening_at_z_omega{2}) (W256.of_int _lookup_s_poly_opening_at_z_omega{2})
   (W256.of_int _lookup_grand_product_opening_at_z_omega{2}) (W256.of_int _lookup_t_poly_opening_at_z{2}) (W256.of_int _lookup_t_poly_opening_at_z_omega{2})
   (W256.of_int _lookup_selector_poly_opening_at_z{2}) (W256.of_int _lookup_table_type_poly_opening_at_z{2}) (W256.of_int _quotient_poly_opening_at_z{2})
   (W256.of_int _linearisation_poly_opening_at_z{2}) (point_of_uint _opening_proof_at_z{2}) (point_of_uint _opening_proof_at_z_omega{2}) 
   (point_of_uint (odflt (0,0) _recursive_part_p1{2})) (point_of_uint (odflt (0,0) _recursive_part_p2{2}))
))
).
wp. call (loadProof_low_equiv_mid_mod mlvk rf).
skip. progress.
rewrite H; smt().
case H6. by progress. progress;
rewrite /loadProof_memory_footprint /point_of_uint
/PROOF_PUBLIC_INPUT /PROOF_STATE_POLYS_0_X_SLOT /PROOF_STATE_POLYS_0_Y_SLOT /PROOF_STATE_POLYS_1_Y_SLOT
/PROOF_STATE_POLYS_2_X_SLOT /PROOF_STATE_POLYS_2_Y_SLOT /PROOF_STATE_POLYS_3_X_SLOT /PROOF_STATE_POLYS_3_Y_SLOT
/PROOF_LOOKUP_S_POLY_X_SLOT /PROOF_LOOKUP_S_POLY_Y_SLOT /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT
/PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT
/PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT /PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT
/PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT
/PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT
/PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
/PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT 
/PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
/PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT
/PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT
/PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
/PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT
/PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT
/PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_1_X_SLOT
/TRANSCRIPT_STATE_0_SLOT 
/TRANSCRIPT_STATE_1_SLOT; progress.
do 44! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux (2^253)); by simplify. 
do 43! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 42! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 41! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 40! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 39! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 38! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 37! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 36! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 33! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 32! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 35! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 34! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 31! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 30! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 29! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 28! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 27! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 26! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 25! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 24! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 23! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 22! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 5! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 21! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 20! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 19! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 18! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 17! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 16! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 15! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 14! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 13! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 12! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 9! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 7! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 6! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 11! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 10! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 8! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 4! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.R); by simplify.
do 3! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 2! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
do 1! (rewrite load_store_diff; [by simplify | by simplify |]); rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.
rewrite load_store_same of_uintK; apply (aux Constants.Q); by simplify.

exists* 
_public_input{2}, _state_poly_0{2}, _state_poly_1{2}, _state_poly_2{2}, _state_poly_3{2}, _copy_permutation_grand_product{2}, _lookup_s_poly{2}, _lookup_grand_product{2},
_quotient_poly_part_0{2}, _quotient_poly_part_1{2}, _quotient_poly_part_2{2}, _quotient_poly_part_3{2}, _state_poly_0_opening_at_z{2}, _state_poly_1_opening_at_z{2},
_state_poly_2_opening_at_z{2}, _state_poly_3_opening_at_z{2}, _state_poly_3_opening_at_z_omega{2}, _gate_selector_0_opening_at_z{2}, _copy_permutation_poly_0_opening_at_z{2},
_copy_permutation_poly_1_opening_at_z{2}, _copy_permutation_poly_2_opening_at_z{2}, _copy_permutation_grand_product_opening_at_z_omega{2}, _lookup_s_poly_opening_at_z_omega{2},
_lookup_grand_product_opening_at_z_omega{2}, _lookup_t_poly_opening_at_z{2}, _lookup_t_poly_opening_at_z_omega{2}, _lookup_selector_poly_opening_at_z{2},
_lookup_table_type_poly_opening_at_z{2}, _quotient_poly_opening_at_z{2}, _linearisation_poly_opening_at_z{2}, _opening_proof_at_z{2}, _opening_proof_at_z_omega{2},
_recursive_part_p1{2}, _recursive_part_p2{2}.
elim*=> 
mod_public_input mod_state_poly_0 mod_state_poly_1 mod_state_poly_2 mod_state_poly_3 mod_copy_permutation_grand_product mod_lookup_s_poly mod_lookup_grand_product
mod_quotient_poly_part_0 mod_quotient_poly_part_1 mod_quotient_poly_part_2 mod_quotient_poly_part_3 mod_state_poly_0_opening_at_z mod_state_poly_1_opening_at_z
mod_state_poly_2_opening_at_z mod_state_poly_3_opening_at_z mod_state_poly_3_opening_at_z_omega mod_gate_selector_0_opening_at_z mod_copy_permutation_poly_0_opening_at_z
mod_copy_permutation_poly_1_opening_at_z mod_copy_permutation_poly_2_opening_at_z mod_copy_permutation_grand_product_opening_at_z_omega mod_lookup_s_poly_opening_at_z_omega
mod_lookup_grand_product_opening_at_z_omega mod_lookup_t_poly_opening_at_z mod_lookup_t_poly_opening_at_z_omega mod_lookup_selector_poly_opening_at_z
mod_lookup_table_type_poly_opening_at_z mod_quotient_poly_opening_at_z mod_linearisation_poly_opening_at_z mod_opening_proof_at_z mod_opening_proof_at_z_omega
mod_recursive_part_p1 mod_recursive_part_p2.

pose mlp :=
loadProof_memory_footprint
   mlvk rf (W256.of_int mod_public_input) (point_of_uint mod_state_poly_0) (point_of_uint mod_state_poly_1) (point_of_uint mod_state_poly_2) (point_of_uint mod_state_poly_3)
   (point_of_uint mod_copy_permutation_grand_product) (point_of_uint mod_lookup_s_poly) (point_of_uint mod_lookup_grand_product) (point_of_uint mod_quotient_poly_part_0)
   (point_of_uint mod_quotient_poly_part_1) (point_of_uint mod_quotient_poly_part_2) (point_of_uint mod_quotient_poly_part_3) (W256.of_int mod_state_poly_0_opening_at_z)
   (W256.of_int mod_state_poly_1_opening_at_z) (W256.of_int mod_state_poly_2_opening_at_z) (W256.of_int mod_state_poly_3_opening_at_z) (W256.of_int mod_state_poly_3_opening_at_z_omega)
   (W256.of_int mod_gate_selector_0_opening_at_z) (W256.of_int mod_copy_permutation_poly_0_opening_at_z) (W256.of_int mod_copy_permutation_poly_1_opening_at_z)
   (W256.of_int mod_copy_permutation_poly_2_opening_at_z) (W256.of_int mod_copy_permutation_grand_product_opening_at_z_omega) (W256.of_int mod_lookup_s_poly_opening_at_z_omega)
   (W256.of_int mod_lookup_grand_product_opening_at_z_omega) (W256.of_int mod_lookup_t_poly_opening_at_z) (W256.of_int mod_lookup_t_poly_opening_at_z_omega)
   (W256.of_int mod_lookup_selector_poly_opening_at_z) (W256.of_int mod_lookup_table_type_poly_opening_at_z) (W256.of_int mod_quotient_poly_opening_at_z)
   (W256.of_int mod_linearisation_poly_opening_at_z) (point_of_uint mod_opening_proof_at_z) (point_of_uint mod_opening_proof_at_z_omega) 
   (point_of_uint (odflt (0,0) mod_recursive_part_p1)) (point_of_uint (odflt (0,0) mod_recursive_part_p2)).

seq 0 0:(
  rf = vk_recursive_flag{2} /\ vk_recursive_flag{2} = false /\
  mod_public_input = _public_input{2} /\
   mod_state_poly_0 = _state_poly_0{2} /\
   mod_state_poly_1 = _state_poly_1{2} /\
   mod_state_poly_2 = _state_poly_2{2} /\
   mod_state_poly_3 = _state_poly_3{2} /\
   mod_copy_permutation_grand_product = _copy_permutation_grand_product{2} /\
   mod_lookup_s_poly = _lookup_s_poly{2} /\
   mod_lookup_grand_product = _lookup_grand_product{2} /\
   mod_quotient_poly_part_0 = _quotient_poly_part_0{2} /\
   mod_quotient_poly_part_1 = _quotient_poly_part_1{2} /\
   mod_quotient_poly_part_2 = _quotient_poly_part_2{2} /\
   mod_quotient_poly_part_3 = _quotient_poly_part_3{2} /\
   mod_state_poly_0_opening_at_z = _state_poly_0_opening_at_z{2} /\
   mod_state_poly_1_opening_at_z = _state_poly_1_opening_at_z{2} /\
   mod_state_poly_2_opening_at_z = _state_poly_2_opening_at_z{2} /\
   mod_state_poly_3_opening_at_z = _state_poly_3_opening_at_z{2} /\
   mod_state_poly_3_opening_at_z_omega = _state_poly_3_opening_at_z_omega{2} /\
   mod_gate_selector_0_opening_at_z = _gate_selector_0_opening_at_z{2} /\
   mod_copy_permutation_poly_0_opening_at_z =
   _copy_permutation_poly_0_opening_at_z{2} /\
   mod_copy_permutation_poly_1_opening_at_z =
   _copy_permutation_poly_1_opening_at_z{2} /\
   mod_copy_permutation_poly_2_opening_at_z =
   _copy_permutation_poly_2_opening_at_z{2} /\
   mod_copy_permutation_grand_product_opening_at_z_omega =
   _copy_permutation_grand_product_opening_at_z_omega{2} /\
   mod_lookup_s_poly_opening_at_z_omega =
   _lookup_s_poly_opening_at_z_omega{2} /\
   mod_lookup_grand_product_opening_at_z_omega =
   _lookup_grand_product_opening_at_z_omega{2} /\
   mod_lookup_t_poly_opening_at_z = _lookup_t_poly_opening_at_z{2} /\
   mod_lookup_t_poly_opening_at_z_omega =
   _lookup_t_poly_opening_at_z_omega{2} /\
   mod_lookup_selector_poly_opening_at_z =
   _lookup_selector_poly_opening_at_z{2} /\
   mod_lookup_table_type_poly_opening_at_z =
   _lookup_table_type_poly_opening_at_z{2} /\
   mod_quotient_poly_opening_at_z = _quotient_poly_opening_at_z{2} /\
   mod_linearisation_poly_opening_at_z = _linearisation_poly_opening_at_z{2} /\
   mod_opening_proof_at_z = _opening_proof_at_z{2} /\
   mod_opening_proof_at_z_omega = _opening_proof_at_z_omega{2} /\
   mod_recursive_part_p1 = _recursive_part_p1{2} /\
   mod_recursive_part_p2 = _recursive_part_p2{2} /\
  public_input_length_in_words{2} = to_uint load_calldata_public_input_length /\
  public_input{2} = to_uint load_calldata_public_input /\
  proof_length_in_words{2} = to_uint load_calldata_proof_length /\
  state_poly_0{2} = point_to_uint load_calldata_state_poly_0 /\
  state_poly_1{2} = point_to_uint load_calldata_state_poly_1 /\
  state_poly_2{2} = point_to_uint load_calldata_state_poly_2 /\
  state_poly_3{2} = point_to_uint load_calldata_state_poly_3 /\
  copy_permutation_grand_product{2} =
  point_to_uint load_calldata_copy_permutation_grand_product /\
  lookup_s_poly{2} = point_to_uint load_calldata_lookup_s_poly /\
  lookup_grand_product{2} = point_to_uint load_calldata_lookup_grand_product /\
  quotient_poly_part_0{2} = point_to_uint load_calldata_quotient_poly_part_0 /\
  quotient_poly_part_1{2} = point_to_uint load_calldata_quotient_poly_part_1 /\
  quotient_poly_part_2{2} = point_to_uint load_calldata_quotient_poly_part_2 /\
  quotient_poly_part_3{2} = point_to_uint load_calldata_quotient_poly_part_3 /\
  state_poly_0_opening_at_z{2} =
  to_uint load_calldata_state_poly_0_opening_at_z /\
  state_poly_1_opening_at_z{2} =
  to_uint load_calldata_state_poly_1_opening_at_z /\
  state_poly_2_opening_at_z{2} =
  to_uint load_calldata_state_poly_2_opening_at_z /\
  state_poly_3_opening_at_z{2} =
  to_uint load_calldata_state_poly_3_opening_at_z /\
  state_poly_3_opening_at_z_omega{2} =
  to_uint load_calldata_state_poly_3_opening_at_z_omega /\
  gate_selector_0_opening_at_z{2} =
  to_uint load_calldata_gate_selector_0_opening_at_z /\
  copy_permutation_poly_0_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_0_opening_at_z /\
  copy_permutation_poly_1_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_1_opening_at_z /\
  copy_permutation_poly_2_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_2_opening_at_z /\
  copy_permutation_grand_product_opening_at_z_omega{2} =
  to_uint load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
  lookup_s_poly_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_s_poly_opening_at_z_omega /\
  lookup_grand_product_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_grand_product_opening_at_z_omega /\
  lookup_t_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_t_poly_opening_at_z /\
  lookup_t_poly_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_t_poly_opening_at_z_omega /\
  lookup_selector_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_selector_poly_opening_at_z /\
  lookup_table_type_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_table_type_poly_opening_at_z /\
  quotient_poly_opening_at_z{2} =
  to_uint load_calldata_quotient_poly_opening_at_z /\
  linearisation_poly_opening_at_z{2} =
  to_uint load_calldata_linearisation_poly_opening_at_z /\
  opening_proof_at_z{2} = point_to_uint load_calldata_opening_proof_at_z /\
  opening_proof_at_z_omega{2} =
  point_to_uint load_calldata_opening_proof_at_z_omega /\
  recursive_proof_length_in_words{2} =
  to_uint load_calldata_recursive_proof_length /\
  recursive_part_p1{2} = point_to_uint load_calldata_recursive_part_p1 /\
  recursive_part_p2{2} = point_to_uint load_calldata_recursive_part_p2 /\
  to_uint (mload mlvk VK_GATE_SETUP_0_X_SLOT) = vk_gate_setup_0X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_0_Y_SLOT) = vk_gate_setup_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_X_SLOT) = vk_gate_setup_1X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_Y_SLOT) = vk_gate_setup_1Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_X_SLOT) = vk_gate_setup_2X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_Y_SLOT) = vk_gate_setup_2Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_X_SLOT) = vk_gate_setup_3X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_Y_SLOT) = vk_gate_setup_3Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_X_SLOT) = vk_gate_setup_4X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_Y_SLOT) = vk_gate_setup_4Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_X_SLOT) = vk_gate_setup_5X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_Y_SLOT) = vk_gate_setup_5Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_X_SLOT) = vk_gate_setup_6X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_Y_SLOT) = vk_gate_setup_6Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_X_SLOT) = vk_gate_setup_7X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_Y_SLOT) = vk_gate_setup_7Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_X_SLOT) = vk_gate_selectors_0X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_Y_SLOT) = vk_gate_selectors_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_X_SLOT) = vk_gate_selectors_1X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_Y_SLOT) = vk_gate_selectors_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_X_SLOT) = vk_permutation_0X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_Y_SLOT) = vk_permutation_0Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_X_SLOT) = vk_permutation_1X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_Y_SLOT) = vk_permutation_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_X_SLOT) = vk_permutation_2X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_Y_SLOT) = vk_permutation_2Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_X_SLOT) = vk_permutation_3X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_Y_SLOT) = vk_permutation_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_X_SLOT) = vk_lookup_table_0X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_Y_SLOT) = vk_lookup_table_0Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_X_SLOT) = vk_lookup_table_1X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_Y_SLOT) = vk_lookup_table_1Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_X_SLOT) = vk_lookup_table_2X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_Y_SLOT) = vk_lookup_table_2Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_X_SLOT) = vk_lookup_table_3X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_Y_SLOT) = vk_lookup_table_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_X_SLOT) = vk_lookup_selector_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_Y_SLOT) = vk_lookup_selector_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_X_SLOT) = vk_lookup_table_type_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) = vk_lookup_table_type_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) = vk_lookup_table_type_Y{2} /\
  mload mlvk VK_RECURSIVE_FLAG_SLOT = uint256_of_bool vk_recursive_flag{2} /\
  to_uint (mload mlvk TRANSCRIPT_STATE_0_SLOT) = 0 /\ (* assumption that EVM memory starts zeroed *)
  to_uint (mload mlvk TRANSCRIPT_STATE_1_SLOT) = 0 /\
 ((Primops.reverted{1} /\ failed{2}) \/
 (!Primops.reverted{1} /\ !failed{2} /\
 (W256.to_uint (mload Primops.memory{1} PROOF_PUBLIC_INPUT) = _public_input{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_0_X_SLOT) = _state_poly_0{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_0_Y_SLOT) = _state_poly_0{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_1_X_SLOT) = _state_poly_1{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_1_Y_SLOT) = _state_poly_1{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_2_X_SLOT) = _state_poly_2{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_2_Y_SLOT) = _state_poly_2{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_3_X_SLOT) = _state_poly_3{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_3_Y_SLOT) = _state_poly_3{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_S_POLY_X_SLOT) = _lookup_s_poly{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_S_POLY_Y_SLOT) = _lookup_s_poly{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT) = _copy_permutation_grand_product{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT) = _copy_permutation_grand_product{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT) = _lookup_grand_product{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT) = _lookup_grand_product{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT) = _quotient_poly_part_0{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT) = _quotient_poly_part_0{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT) = _quotient_poly_part_1{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT) = _quotient_poly_part_1{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT) = _quotient_poly_part_2{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT) = _quotient_poly_part_2{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT) = _quotient_poly_part_3{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT) = _quotient_poly_part_3{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = _quotient_poly_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = _state_poly_0_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = _state_poly_1_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = _state_poly_2_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = _state_poly_3_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) = _state_poly_3_opening_at_z_omega{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = _gate_selector_0_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = _copy_permutation_poly_0_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = _copy_permutation_poly_1_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = _copy_permutation_poly_2_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = _copy_permutation_grand_product_opening_at_z_omega{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) = _lookup_t_poly_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) = _lookup_selector_poly_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) = _lookup_table_type_poly_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = _lookup_s_poly_opening_at_z_omega{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = _lookup_grand_product_opening_at_z_omega{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) = _lookup_t_poly_opening_at_z_omega{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = _linearisation_poly_opening_at_z{2} /\
  W256.to_uint (mload Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_X_SLOT) = _opening_proof_at_z{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_Y_SLOT) = _opening_proof_at_z{2}.`2 /\
  W256.to_uint (mload Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT) = _opening_proof_at_z_omega{2}.`1 /\
  W256.to_uint (mload Primops.memory{1} PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT) = _opening_proof_at_z_omega{2}.`2 /\
  Primops.memory{1} = mlp
)))
).
skip; progress.
rewrite H0. reflexivity. rewrite H1. reflexivity.
case H2. 
move=>AAA. left. exact AAA.
move=>AAA. right. progress.

seq 0 0:(
  rf = vk_recursive_flag{2} /\ vk_recursive_flag{2} = false /\
  mod_public_input = _public_input{2} /\
   mod_state_poly_0 = _state_poly_0{2} /\
   mod_state_poly_1 = _state_poly_1{2} /\
   mod_state_poly_2 = _state_poly_2{2} /\
   mod_state_poly_3 = _state_poly_3{2} /\
   mod_copy_permutation_grand_product = _copy_permutation_grand_product{2} /\
   mod_lookup_s_poly = _lookup_s_poly{2} /\
   mod_lookup_grand_product = _lookup_grand_product{2} /\
   mod_quotient_poly_part_0 = _quotient_poly_part_0{2} /\
   mod_quotient_poly_part_1 = _quotient_poly_part_1{2} /\
   mod_quotient_poly_part_2 = _quotient_poly_part_2{2} /\
   mod_quotient_poly_part_3 = _quotient_poly_part_3{2} /\
   mod_state_poly_0_opening_at_z = _state_poly_0_opening_at_z{2} /\
   mod_state_poly_1_opening_at_z = _state_poly_1_opening_at_z{2} /\
   mod_state_poly_2_opening_at_z = _state_poly_2_opening_at_z{2} /\
   mod_state_poly_3_opening_at_z = _state_poly_3_opening_at_z{2} /\
   mod_state_poly_3_opening_at_z_omega = _state_poly_3_opening_at_z_omega{2} /\
   mod_gate_selector_0_opening_at_z = _gate_selector_0_opening_at_z{2} /\
   mod_copy_permutation_poly_0_opening_at_z =
   _copy_permutation_poly_0_opening_at_z{2} /\
   mod_copy_permutation_poly_1_opening_at_z =
   _copy_permutation_poly_1_opening_at_z{2} /\
   mod_copy_permutation_poly_2_opening_at_z =
   _copy_permutation_poly_2_opening_at_z{2} /\
   mod_copy_permutation_grand_product_opening_at_z_omega =
   _copy_permutation_grand_product_opening_at_z_omega{2} /\
   mod_lookup_s_poly_opening_at_z_omega =
   _lookup_s_poly_opening_at_z_omega{2} /\
   mod_lookup_grand_product_opening_at_z_omega =
   _lookup_grand_product_opening_at_z_omega{2} /\
   mod_lookup_t_poly_opening_at_z = _lookup_t_poly_opening_at_z{2} /\
   mod_lookup_t_poly_opening_at_z_omega =
   _lookup_t_poly_opening_at_z_omega{2} /\
   mod_lookup_selector_poly_opening_at_z =
   _lookup_selector_poly_opening_at_z{2} /\
   mod_lookup_table_type_poly_opening_at_z =
   _lookup_table_type_poly_opening_at_z{2} /\
   mod_quotient_poly_opening_at_z = _quotient_poly_opening_at_z{2} /\
   mod_linearisation_poly_opening_at_z = _linearisation_poly_opening_at_z{2} /\
   mod_opening_proof_at_z = _opening_proof_at_z{2} /\
   mod_opening_proof_at_z_omega = _opening_proof_at_z_omega{2} /\
   mod_recursive_part_p1 = _recursive_part_p1{2} /\
   mod_recursive_part_p2 = _recursive_part_p2{2} /\
  public_input_length_in_words{2} = to_uint load_calldata_public_input_length /\
  public_input{2} = to_uint load_calldata_public_input /\
  proof_length_in_words{2} = to_uint load_calldata_proof_length /\
  state_poly_0{2} = point_to_uint load_calldata_state_poly_0 /\
  state_poly_1{2} = point_to_uint load_calldata_state_poly_1 /\
  state_poly_2{2} = point_to_uint load_calldata_state_poly_2 /\
  state_poly_3{2} = point_to_uint load_calldata_state_poly_3 /\
  copy_permutation_grand_product{2} =
  point_to_uint load_calldata_copy_permutation_grand_product /\
  lookup_s_poly{2} = point_to_uint load_calldata_lookup_s_poly /\
  lookup_grand_product{2} = point_to_uint load_calldata_lookup_grand_product /\
  quotient_poly_part_0{2} = point_to_uint load_calldata_quotient_poly_part_0 /\
  quotient_poly_part_1{2} = point_to_uint load_calldata_quotient_poly_part_1 /\
  quotient_poly_part_2{2} = point_to_uint load_calldata_quotient_poly_part_2 /\
  quotient_poly_part_3{2} = point_to_uint load_calldata_quotient_poly_part_3 /\
  state_poly_0_opening_at_z{2} =
  to_uint load_calldata_state_poly_0_opening_at_z /\
  state_poly_1_opening_at_z{2} =
  to_uint load_calldata_state_poly_1_opening_at_z /\
  state_poly_2_opening_at_z{2} =
  to_uint load_calldata_state_poly_2_opening_at_z /\
  state_poly_3_opening_at_z{2} =
  to_uint load_calldata_state_poly_3_opening_at_z /\
  state_poly_3_opening_at_z_omega{2} =
  to_uint load_calldata_state_poly_3_opening_at_z_omega /\
  gate_selector_0_opening_at_z{2} =
  to_uint load_calldata_gate_selector_0_opening_at_z /\
  copy_permutation_poly_0_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_0_opening_at_z /\
  copy_permutation_poly_1_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_1_opening_at_z /\
  copy_permutation_poly_2_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_2_opening_at_z /\
  copy_permutation_grand_product_opening_at_z_omega{2} =
  to_uint load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
  lookup_s_poly_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_s_poly_opening_at_z_omega /\
  lookup_grand_product_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_grand_product_opening_at_z_omega /\
  lookup_t_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_t_poly_opening_at_z /\
  lookup_t_poly_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_t_poly_opening_at_z_omega /\
  lookup_selector_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_selector_poly_opening_at_z /\
  lookup_table_type_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_table_type_poly_opening_at_z /\
  quotient_poly_opening_at_z{2} =
  to_uint load_calldata_quotient_poly_opening_at_z /\
  linearisation_poly_opening_at_z{2} =
  to_uint load_calldata_linearisation_poly_opening_at_z /\
  opening_proof_at_z{2} = point_to_uint load_calldata_opening_proof_at_z /\
  opening_proof_at_z_omega{2} =
  point_to_uint load_calldata_opening_proof_at_z_omega /\
  recursive_proof_length_in_words{2} =
  to_uint load_calldata_recursive_proof_length /\
  recursive_part_p1{2} = point_to_uint load_calldata_recursive_part_p1 /\
  recursive_part_p2{2} = point_to_uint load_calldata_recursive_part_p2 /\
  to_uint (mload mlvk VK_GATE_SETUP_0_X_SLOT) = vk_gate_setup_0X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_0_Y_SLOT) = vk_gate_setup_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_X_SLOT) = vk_gate_setup_1X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_Y_SLOT) = vk_gate_setup_1Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_X_SLOT) = vk_gate_setup_2X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_Y_SLOT) = vk_gate_setup_2Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_X_SLOT) = vk_gate_setup_3X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_Y_SLOT) = vk_gate_setup_3Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_X_SLOT) = vk_gate_setup_4X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_Y_SLOT) = vk_gate_setup_4Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_X_SLOT) = vk_gate_setup_5X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_Y_SLOT) = vk_gate_setup_5Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_X_SLOT) = vk_gate_setup_6X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_Y_SLOT) = vk_gate_setup_6Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_X_SLOT) = vk_gate_setup_7X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_Y_SLOT) = vk_gate_setup_7Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_X_SLOT) = vk_gate_selectors_0X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_Y_SLOT) = vk_gate_selectors_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_X_SLOT) = vk_gate_selectors_1X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_Y_SLOT) = vk_gate_selectors_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_X_SLOT) = vk_permutation_0X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_Y_SLOT) = vk_permutation_0Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_X_SLOT) = vk_permutation_1X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_Y_SLOT) = vk_permutation_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_X_SLOT) = vk_permutation_2X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_Y_SLOT) = vk_permutation_2Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_X_SLOT) = vk_permutation_3X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_Y_SLOT) = vk_permutation_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_X_SLOT) = vk_lookup_table_0X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_Y_SLOT) = vk_lookup_table_0Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_X_SLOT) = vk_lookup_table_1X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_Y_SLOT) = vk_lookup_table_1Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_X_SLOT) = vk_lookup_table_2X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_Y_SLOT) = vk_lookup_table_2Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_X_SLOT) = vk_lookup_table_3X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_Y_SLOT) = vk_lookup_table_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_X_SLOT) = vk_lookup_selector_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_Y_SLOT) = vk_lookup_selector_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_X_SLOT) = vk_lookup_table_type_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) = vk_lookup_table_type_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) = vk_lookup_table_type_Y{2} /\
  mload mlvk VK_RECURSIVE_FLAG_SLOT = uint256_of_bool vk_recursive_flag{2} /\
  to_uint (mload mlvk TRANSCRIPT_STATE_0_SLOT) = 0 /\ (* assumption that EVM memory starts zeroed *)
  to_uint (mload mlvk TRANSCRIPT_STATE_1_SLOT) = 0 /\
 ((Primops.reverted{1} /\ failed{2}) \/
 (!Primops.reverted{1} /\ !failed{2} /\
 (W256.to_uint (mload mlp PROOF_PUBLIC_INPUT) = _public_input{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_0_X_SLOT) = _state_poly_0{2}.`1 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_0_Y_SLOT) = _state_poly_0{2}.`2 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_1_X_SLOT) = _state_poly_1{2}.`1 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_1_Y_SLOT) = _state_poly_1{2}.`2 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_2_X_SLOT) = _state_poly_2{2}.`1 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_2_Y_SLOT) = _state_poly_2{2}.`2 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_3_X_SLOT) = _state_poly_3{2}.`1 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_3_Y_SLOT) = _state_poly_3{2}.`2 /\
  W256.to_uint (mload mlp PROOF_LOOKUP_S_POLY_X_SLOT) = _lookup_s_poly{2}.`1 /\
  W256.to_uint (mload mlp PROOF_LOOKUP_S_POLY_Y_SLOT) = _lookup_s_poly{2}.`2 /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT) = _copy_permutation_grand_product{2}.`1 /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT) = _copy_permutation_grand_product{2}.`2 /\
  W256.to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT) = _lookup_grand_product{2}.`1 /\
  W256.to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT) = _lookup_grand_product{2}.`2 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT) = _quotient_poly_part_0{2}.`1 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT) = _quotient_poly_part_0{2}.`2 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT) = _quotient_poly_part_1{2}.`1 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT) = _quotient_poly_part_1{2}.`2 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT) = _quotient_poly_part_2{2}.`1 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT) = _quotient_poly_part_2{2}.`2 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT) = _quotient_poly_part_3{2}.`1 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT) = _quotient_poly_part_3{2}.`2 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = _quotient_poly_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = _state_poly_0_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = _state_poly_1_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = _state_poly_2_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = _state_poly_3_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) = _state_poly_3_opening_at_z_omega{2} /\
  W256.to_uint (mload mlp PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = _gate_selector_0_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = _copy_permutation_poly_0_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = _copy_permutation_poly_1_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = _copy_permutation_poly_2_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = _copy_permutation_grand_product_opening_at_z_omega{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) = _lookup_t_poly_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) = _lookup_selector_poly_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) = _lookup_table_type_poly_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = _lookup_s_poly_opening_at_z_omega{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = _lookup_grand_product_opening_at_z_omega{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) = _lookup_t_poly_opening_at_z_omega{2} /\
  W256.to_uint (mload mlp PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = _linearisation_poly_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_X_SLOT) = _opening_proof_at_z{2}.`1 /\
  W256.to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_Y_SLOT) = _opening_proof_at_z{2}.`2 /\
  W256.to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT) = _opening_proof_at_z_omega{2}.`1 /\
  W256.to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT) = _opening_proof_at_z_omega{2}.`2 /\
  Primops.memory{1} = mlp
)))
).
skip. progress.
case H2. 
move=>AAA. left. exact AAA.
move=>[? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]. right.
have HHH: Primops.memory{1} = mlp. by progress.
rewrite -HHH. by progress.

seq 1 1:(
  rf = vk_recursive_flag{2} /\
  vk_recursive_flag{2} = false /\
  mod_public_input = _public_input{2} /\
  mod_state_poly_0 = _state_poly_0{2} /\
  mod_state_poly_1 = _state_poly_1{2} /\
  mod_state_poly_2 = _state_poly_2{2} /\
  mod_state_poly_3 = _state_poly_3{2} /\
  mod_copy_permutation_grand_product = _copy_permutation_grand_product{2} /\
  mod_lookup_s_poly = _lookup_s_poly{2} /\
  mod_lookup_grand_product = _lookup_grand_product{2} /\
  mod_quotient_poly_part_0 = _quotient_poly_part_0{2} /\
  mod_quotient_poly_part_1 = _quotient_poly_part_1{2} /\
  mod_quotient_poly_part_2 = _quotient_poly_part_2{2} /\
  mod_quotient_poly_part_3 = _quotient_poly_part_3{2} /\
  mod_state_poly_0_opening_at_z = _state_poly_0_opening_at_z{2} /\
  mod_state_poly_1_opening_at_z = _state_poly_1_opening_at_z{2} /\
  mod_state_poly_2_opening_at_z = _state_poly_2_opening_at_z{2} /\
  mod_state_poly_3_opening_at_z = _state_poly_3_opening_at_z{2} /\
  mod_state_poly_3_opening_at_z_omega = _state_poly_3_opening_at_z_omega{2} /\
  mod_gate_selector_0_opening_at_z = _gate_selector_0_opening_at_z{2} /\
  mod_copy_permutation_poly_0_opening_at_z =
  _copy_permutation_poly_0_opening_at_z{2} /\
  mod_copy_permutation_poly_1_opening_at_z =
  _copy_permutation_poly_1_opening_at_z{2} /\
  mod_copy_permutation_poly_2_opening_at_z =
  _copy_permutation_poly_2_opening_at_z{2} /\
  mod_copy_permutation_grand_product_opening_at_z_omega =
  _copy_permutation_grand_product_opening_at_z_omega{2} /\
  mod_lookup_s_poly_opening_at_z_omega = _lookup_s_poly_opening_at_z_omega{2} /\
  mod_lookup_grand_product_opening_at_z_omega =
  _lookup_grand_product_opening_at_z_omega{2} /\
  mod_lookup_t_poly_opening_at_z = _lookup_t_poly_opening_at_z{2} /\
  mod_lookup_t_poly_opening_at_z_omega = _lookup_t_poly_opening_at_z_omega{2} /\
  mod_lookup_selector_poly_opening_at_z =
  _lookup_selector_poly_opening_at_z{2} /\
  mod_lookup_table_type_poly_opening_at_z =
  _lookup_table_type_poly_opening_at_z{2} /\
  mod_quotient_poly_opening_at_z = _quotient_poly_opening_at_z{2} /\
  mod_linearisation_poly_opening_at_z = _linearisation_poly_opening_at_z{2} /\
  mod_opening_proof_at_z = _opening_proof_at_z{2} /\
  mod_opening_proof_at_z_omega = _opening_proof_at_z_omega{2} /\
  mod_recursive_part_p1 = _recursive_part_p1{2} /\
  mod_recursive_part_p2 = _recursive_part_p2{2} /\
  public_input_length_in_words{2} = to_uint load_calldata_public_input_length /\
  public_input{2} = to_uint load_calldata_public_input /\
  proof_length_in_words{2} = to_uint load_calldata_proof_length /\
  state_poly_0{2} = point_to_uint load_calldata_state_poly_0 /\
  state_poly_1{2} = point_to_uint load_calldata_state_poly_1 /\
  state_poly_2{2} = point_to_uint load_calldata_state_poly_2 /\
  state_poly_3{2} = point_to_uint load_calldata_state_poly_3 /\
  copy_permutation_grand_product{2} =
  point_to_uint load_calldata_copy_permutation_grand_product /\
  lookup_s_poly{2} = point_to_uint load_calldata_lookup_s_poly /\
  lookup_grand_product{2} = point_to_uint load_calldata_lookup_grand_product /\
  quotient_poly_part_0{2} = point_to_uint load_calldata_quotient_poly_part_0 /\
  quotient_poly_part_1{2} = point_to_uint load_calldata_quotient_poly_part_1 /\
  quotient_poly_part_2{2} = point_to_uint load_calldata_quotient_poly_part_2 /\
  quotient_poly_part_3{2} = point_to_uint load_calldata_quotient_poly_part_3 /\
  state_poly_0_opening_at_z{2} =
  to_uint load_calldata_state_poly_0_opening_at_z /\
  state_poly_1_opening_at_z{2} =
  to_uint load_calldata_state_poly_1_opening_at_z /\
  state_poly_2_opening_at_z{2} =
  to_uint load_calldata_state_poly_2_opening_at_z /\
  state_poly_3_opening_at_z{2} =
  to_uint load_calldata_state_poly_3_opening_at_z /\
  state_poly_3_opening_at_z_omega{2} =
  to_uint load_calldata_state_poly_3_opening_at_z_omega /\
  gate_selector_0_opening_at_z{2} =
  to_uint load_calldata_gate_selector_0_opening_at_z /\
  copy_permutation_poly_0_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_0_opening_at_z /\
  copy_permutation_poly_1_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_1_opening_at_z /\
  copy_permutation_poly_2_opening_at_z{2} =
  to_uint load_calldata_copy_permutation_poly_2_opening_at_z /\
  copy_permutation_grand_product_opening_at_z_omega{2} =
  to_uint load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
  lookup_s_poly_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_s_poly_opening_at_z_omega /\
  lookup_grand_product_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_grand_product_opening_at_z_omega /\
  lookup_t_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_t_poly_opening_at_z /\
  lookup_t_poly_opening_at_z_omega{2} =
  to_uint load_calldata_lookup_t_poly_opening_at_z_omega /\
  lookup_selector_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_selector_poly_opening_at_z /\
  lookup_table_type_poly_opening_at_z{2} =
  to_uint load_calldata_lookup_table_type_poly_opening_at_z /\
  quotient_poly_opening_at_z{2} =
  to_uint load_calldata_quotient_poly_opening_at_z /\
  linearisation_poly_opening_at_z{2} =
  to_uint load_calldata_linearisation_poly_opening_at_z /\
  opening_proof_at_z{2} = point_to_uint load_calldata_opening_proof_at_z /\
  opening_proof_at_z_omega{2} =
  point_to_uint load_calldata_opening_proof_at_z_omega /\
  recursive_proof_length_in_words{2} =
  to_uint load_calldata_recursive_proof_length /\
  recursive_part_p1{2} = point_to_uint load_calldata_recursive_part_p1 /\
  recursive_part_p2{2} = point_to_uint load_calldata_recursive_part_p2 /\
  to_uint (mload mlvk VK_GATE_SETUP_0_X_SLOT) = vk_gate_setup_0X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_0_Y_SLOT) = vk_gate_setup_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_X_SLOT) = vk_gate_setup_1X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_Y_SLOT) = vk_gate_setup_1Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_X_SLOT) = vk_gate_setup_2X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_Y_SLOT) = vk_gate_setup_2Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_X_SLOT) = vk_gate_setup_3X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_Y_SLOT) = vk_gate_setup_3Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_X_SLOT) = vk_gate_setup_4X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_Y_SLOT) = vk_gate_setup_4Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_X_SLOT) = vk_gate_setup_5X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_Y_SLOT) = vk_gate_setup_5Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_X_SLOT) = vk_gate_setup_6X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_Y_SLOT) = vk_gate_setup_6Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_X_SLOT) = vk_gate_setup_7X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_Y_SLOT) = vk_gate_setup_7Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_X_SLOT) = vk_gate_selectors_0X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_Y_SLOT) = vk_gate_selectors_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_X_SLOT) = vk_gate_selectors_1X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_Y_SLOT) = vk_gate_selectors_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_X_SLOT) = vk_permutation_0X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_Y_SLOT) = vk_permutation_0Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_X_SLOT) = vk_permutation_1X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_Y_SLOT) = vk_permutation_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_X_SLOT) = vk_permutation_2X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_Y_SLOT) = vk_permutation_2Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_X_SLOT) = vk_permutation_3X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_Y_SLOT) = vk_permutation_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_X_SLOT) = vk_lookup_table_0X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_Y_SLOT) = vk_lookup_table_0Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_X_SLOT) = vk_lookup_table_1X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_Y_SLOT) = vk_lookup_table_1Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_X_SLOT) = vk_lookup_table_2X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_Y_SLOT) = vk_lookup_table_2Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_X_SLOT) = vk_lookup_table_3X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_Y_SLOT) = vk_lookup_table_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_X_SLOT) = vk_lookup_selector_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_Y_SLOT) = vk_lookup_selector_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_X_SLOT) =
  vk_lookup_table_type_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) =
  vk_lookup_table_type_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) =
  vk_lookup_table_type_Y{2} /\
  mload mlvk VK_RECURSIVE_FLAG_SLOT = uint256_of_bool vk_recursive_flag{2} /\
  to_uint (mload mlvk TRANSCRIPT_STATE_0_SLOT) = 0 /\
  to_uint (mload mlvk TRANSCRIPT_STATE_1_SLOT) = 0 /\
  ((Primops.reverted{1} /\ failed{2}) \/
    (!Primops.reverted{1} /\ !failed{2} /\
    W256.to_uint (mload mlp PROOF_PUBLIC_INPUT) = _public_input{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_0_X_SLOT) = _state_poly_0{2}.`1 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_0_Y_SLOT) = _state_poly_0{2}.`2 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_1_X_SLOT) = _state_poly_1{2}.`1 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_1_Y_SLOT) = _state_poly_1{2}.`2 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_2_X_SLOT) = _state_poly_2{2}.`1 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_2_Y_SLOT) = _state_poly_2{2}.`2 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_3_X_SLOT) = _state_poly_3{2}.`1 /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_3_Y_SLOT) = _state_poly_3{2}.`2 /\
  W256.to_uint (mload mlp PROOF_LOOKUP_S_POLY_X_SLOT) = _lookup_s_poly{2}.`1 /\
  W256.to_uint (mload mlp PROOF_LOOKUP_S_POLY_Y_SLOT) = _lookup_s_poly{2}.`2 /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT) = _copy_permutation_grand_product{2}.`1 /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT) = _copy_permutation_grand_product{2}.`2 /\
  W256.to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT) = _lookup_grand_product{2}.`1 /\
  W256.to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT) = _lookup_grand_product{2}.`2 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT) = _quotient_poly_part_0{2}.`1 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT) = _quotient_poly_part_0{2}.`2 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT) = _quotient_poly_part_1{2}.`1 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT) = _quotient_poly_part_1{2}.`2 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT) = _quotient_poly_part_2{2}.`1 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT) = _quotient_poly_part_2{2}.`2 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT) = _quotient_poly_part_3{2}.`1 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT) = _quotient_poly_part_3{2}.`2 /\
  W256.to_uint (mload mlp PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) = _quotient_poly_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = _state_poly_0_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = _state_poly_1_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = _state_poly_2_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = _state_poly_3_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) = _state_poly_3_opening_at_z_omega{2} /\
  W256.to_uint (mload mlp PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) = _gate_selector_0_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = _copy_permutation_poly_0_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = _copy_permutation_poly_1_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = _copy_permutation_poly_2_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = _copy_permutation_grand_product_opening_at_z_omega{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) = _lookup_t_poly_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) = _lookup_selector_poly_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) = _lookup_table_type_poly_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) = _lookup_s_poly_opening_at_z_omega{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = _lookup_grand_product_opening_at_z_omega{2} /\
  W256.to_uint (mload mlp PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) = _lookup_t_poly_opening_at_z_omega{2} /\
  W256.to_uint (mload mlp PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) = _linearisation_poly_opening_at_z{2} /\
  W256.to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_X_SLOT) = _opening_proof_at_z{2}.`1 /\
  W256.to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_Y_SLOT) = _opening_proof_at_z{2}.`2 /\
  W256.to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT) = _opening_proof_at_z_omega{2}.`1 /\
  W256.to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT) = _opening_proof_at_z_omega{2}.`2 /\
  0 <= state_alpha{2} < 2^253 /\ 
  0 <= state_beta{2} < 2^253 /\ 
  0 <= state_beta_lookup{2} < 2^253 /\ 
  0 <= state_gamma{2} < 2^253 /\
  0 <= state_gamma_lookup{2} < 2^253 /\ 
  0 <= state_eta{2} < 2^253 /\ 
  0 <= state_z{2} < 2^253 /\ 
  0 <= state_z_in_domain{2} < Constants.R /\
  0 <= state_v{2} < 2^253 /\ 0 <= state_u{2} < 2^253 /\ 
  exists (s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21: uint256), Primops.memory{1} = initializeTranscript_memory_footprint mlp
     (W256.of_int state_eta{2}) (W256.of_int state_beta{2}) (W256.of_int state_gamma{2}) (W256.of_int state_beta_lookup{2}) (W256.of_int state_gamma_lookup{2}) (W256.of_int state_alpha{2})
     (W256.of_int state_z{2}) (W256.of_int state_z_in_domain{2}) (W256.of_int state_v{2}) (W256.of_int state_u{2})
       s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21
))
).
exists* Primops.reverted{1}. elim*=> reverted.
case reverted. progress.
conseq (_ : Primops.reverted{1} /\ failed{2}  ==> Primops.reverted{1} /\ failed{2}).
progress. case H2. by progress. by progress.
progress. left. by progress.
inline InitializeTranscript.mid UpdateTranscript.UpdateTranscript.mid GetTranscriptChallenge.GetTranscriptChallenge.mid Modexp.Modexp.mid. wp.
call{1} initializeTranscript_low_pspec_revert.
skip. simplify. progress.

call (unitializeTranscript_low_equiv_mid mlp 0 0 
mod_public_input 
mod_state_poly_0.`1 mod_state_poly_0.`2 
mod_state_poly_1.`1 mod_state_poly_1.`2 
mod_state_poly_2.`1 mod_state_poly_2.`2 
mod_state_poly_3.`1 mod_state_poly_3.`2 
mod_lookup_s_poly.`1 mod_lookup_s_poly.`2 
mod_copy_permutation_grand_product.`1 mod_copy_permutation_grand_product.`2 
mod_lookup_grand_product.`1 mod_lookup_grand_product.`2 
mod_quotient_poly_part_0.`1 mod_quotient_poly_part_0.`2 
mod_quotient_poly_part_1.`1 mod_quotient_poly_part_1.`2 
mod_quotient_poly_part_2.`1 mod_quotient_poly_part_2.`2 
mod_quotient_poly_part_3.`1 mod_quotient_poly_part_3.`2 
mod_quotient_poly_opening_at_z 
mod_state_poly_0_opening_at_z 
mod_state_poly_1_opening_at_z 
mod_state_poly_2_opening_at_z 
mod_state_poly_3_opening_at_z 
mod_state_poly_3_opening_at_z_omega 
mod_gate_selector_0_opening_at_z 
mod_copy_permutation_poly_0_opening_at_z 
mod_copy_permutation_poly_1_opening_at_z 
mod_copy_permutation_poly_2_opening_at_z 
mod_copy_permutation_grand_product_opening_at_z_omega 
mod_lookup_t_poly_opening_at_z 
mod_lookup_selector_poly_opening_at_z 
mod_lookup_table_type_poly_opening_at_z 
mod_lookup_s_poly_opening_at_z_omega 
mod_lookup_grand_product_opening_at_z_omega 
mod_lookup_t_poly_opening_at_z_omega 
mod_linearisation_poly_opening_at_z 
mod_opening_proof_at_z.`1 mod_opening_proof_at_z.`2 
mod_opening_proof_at_z_omega.`1 mod_opening_proof_at_z_omega.`2).
skip. progress; case H2; progress.

rewrite /mlp /loadProof_memory_footprint
/PROOF_PUBLIC_INPUT /PROOF_STATE_POLYS_0_X_SLOT /PROOF_STATE_POLYS_0_Y_SLOT /PROOF_STATE_POLYS_1_Y_SLOT
/PROOF_STATE_POLYS_2_X_SLOT /PROOF_STATE_POLYS_2_Y_SLOT /PROOF_STATE_POLYS_3_X_SLOT /PROOF_STATE_POLYS_3_Y_SLOT
/PROOF_LOOKUP_S_POLY_X_SLOT /PROOF_LOOKUP_S_POLY_Y_SLOT /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT
/PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT
/PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT /PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT
/PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT
/PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT
/PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
/PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT 
/PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
/PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT
/PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT
/PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
/PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT
/PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT
/PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_1_X_SLOT
/TRANSCRIPT_STATE_0_SLOT 
/TRANSCRIPT_STATE_1_SLOT; progress.
do 45! (rewrite load_store_diff; [by simplify | by simplify |]). by progress.

rewrite /mlp /loadProof_memory_footprint
/PROOF_PUBLIC_INPUT /PROOF_STATE_POLYS_0_X_SLOT /PROOF_STATE_POLYS_0_Y_SLOT /PROOF_STATE_POLYS_1_Y_SLOT
/PROOF_STATE_POLYS_2_X_SLOT /PROOF_STATE_POLYS_2_Y_SLOT /PROOF_STATE_POLYS_3_X_SLOT /PROOF_STATE_POLYS_3_Y_SLOT
/PROOF_LOOKUP_S_POLY_X_SLOT /PROOF_LOOKUP_S_POLY_Y_SLOT /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT
/PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT
/PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT /PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT
/PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT
/PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT
/PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
/PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT 
/PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
/PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT
/PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT
/PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
/PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT
/PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT
/PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_1_X_SLOT
/TRANSCRIPT_STATE_0_SLOT 
/TRANSCRIPT_STATE_1_SLOT; progress.
do 45! (rewrite load_store_diff; [by simplify | by simplify |]). by progress.
right. progress.
exists s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21. reflexivity.

exists* state_alpha{2}, state_beta{2}, state_beta_lookup{2}, state_gamma{2}, state_gamma_lookup{2}, state_eta{2}, state_z{2}, state_z_in_domain{2}, state_v{2}, state_u{2}.
elim*=> alpha_r beta_r beta_lookup_r gamma_r gamma_lookup_r eta_r z_r z_in_domain_r v_r u_r.
progress.
pose mit := 
initializeTranscript_memory_footprint mlp ((of_int eta_r))%W256
     ((of_int beta_r))%W256 ((of_int gamma_r))%W256
     ((of_int beta_lookup_r))%W256
     ((of_int gamma_lookup_r))%W256 ((of_int alpha_r))%W256
     ((of_int z_r))%W256 ((of_int z_in_domain_r))%W256
     ((of_int v_r))%W256 ((of_int u_r))%W256 s1 s2 s3 s4 s5 s6
     s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21.

seq 0 0:(
alpha_r = state_alpha{2} /\
       beta_r = state_beta{2} /\
   beta_lookup_r = state_beta_lookup{2} /\
   gamma_r = state_gamma{2} /\
   gamma_lookup_r = state_gamma_lookup{2} /\
   eta_r = state_eta{2} /\
   z_r = state_z{2} /\
   z_in_domain_r = state_z_in_domain{2} /\
   v_r = state_v{2} /\ u_r = state_u{2} /\
  rf = vk_recursive_flag{2} /\
  vk_recursive_flag{2} = false /\
  mod_public_input = _public_input{2} /\
  mod_state_poly_0 = _state_poly_0{2} /\
  mod_state_poly_1 = _state_poly_1{2} /\
  mod_state_poly_2 = _state_poly_2{2} /\
  mod_state_poly_3 = _state_poly_3{2} /\
  mod_copy_permutation_grand_product = _copy_permutation_grand_product{2} /\
  mod_lookup_s_poly = _lookup_s_poly{2} /\
  mod_lookup_grand_product = _lookup_grand_product{2} /\
  mod_quotient_poly_part_0 = _quotient_poly_part_0{2} /\
  mod_quotient_poly_part_1 = _quotient_poly_part_1{2} /\
  mod_quotient_poly_part_2 = _quotient_poly_part_2{2} /\
  mod_quotient_poly_part_3 = _quotient_poly_part_3{2} /\
  mod_state_poly_0_opening_at_z = _state_poly_0_opening_at_z{2} /\
  mod_state_poly_1_opening_at_z = _state_poly_1_opening_at_z{2} /\
  mod_state_poly_2_opening_at_z = _state_poly_2_opening_at_z{2} /\
  mod_state_poly_3_opening_at_z = _state_poly_3_opening_at_z{2} /\
  mod_state_poly_3_opening_at_z_omega = _state_poly_3_opening_at_z_omega{2} /\
  mod_gate_selector_0_opening_at_z = _gate_selector_0_opening_at_z{2} /\
  mod_copy_permutation_poly_0_opening_at_z =
  _copy_permutation_poly_0_opening_at_z{2} /\
  mod_copy_permutation_poly_1_opening_at_z =
  _copy_permutation_poly_1_opening_at_z{2} /\
  mod_copy_permutation_poly_2_opening_at_z =
  _copy_permutation_poly_2_opening_at_z{2} /\
  mod_copy_permutation_grand_product_opening_at_z_omega =
  _copy_permutation_grand_product_opening_at_z_omega{2} /\
  mod_lookup_s_poly_opening_at_z_omega = _lookup_s_poly_opening_at_z_omega{2} /\
  mod_lookup_grand_product_opening_at_z_omega =
  _lookup_grand_product_opening_at_z_omega{2} /\
  mod_lookup_t_poly_opening_at_z = _lookup_t_poly_opening_at_z{2} /\
  mod_lookup_t_poly_opening_at_z_omega = _lookup_t_poly_opening_at_z_omega{2} /\
  mod_lookup_selector_poly_opening_at_z =
  _lookup_selector_poly_opening_at_z{2} /\
  mod_lookup_table_type_poly_opening_at_z =
  _lookup_table_type_poly_opening_at_z{2} /\
  mod_quotient_poly_opening_at_z = _quotient_poly_opening_at_z{2} /\
  mod_linearisation_poly_opening_at_z = _linearisation_poly_opening_at_z{2} /\
  mod_opening_proof_at_z = _opening_proof_at_z{2} /\
  mod_opening_proof_at_z_omega = _opening_proof_at_z_omega{2} /\
  mod_recursive_part_p1 = _recursive_part_p1{2} /\
  mod_recursive_part_p2 = _recursive_part_p2{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_0_X_SLOT) = vk_gate_setup_0X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_0_Y_SLOT) = vk_gate_setup_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_X_SLOT) = vk_gate_setup_1X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_Y_SLOT) = vk_gate_setup_1Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_X_SLOT) = vk_gate_setup_2X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_Y_SLOT) = vk_gate_setup_2Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_X_SLOT) = vk_gate_setup_3X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_Y_SLOT) = vk_gate_setup_3Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_X_SLOT) = vk_gate_setup_4X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_Y_SLOT) = vk_gate_setup_4Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_X_SLOT) = vk_gate_setup_5X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_Y_SLOT) = vk_gate_setup_5Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_X_SLOT) = vk_gate_setup_6X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_Y_SLOT) = vk_gate_setup_6Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_X_SLOT) = vk_gate_setup_7X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_Y_SLOT) = vk_gate_setup_7Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_X_SLOT) = vk_gate_selectors_0X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_Y_SLOT) = vk_gate_selectors_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_X_SLOT) = vk_gate_selectors_1X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_Y_SLOT) = vk_gate_selectors_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_X_SLOT) = vk_permutation_0X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_Y_SLOT) = vk_permutation_0Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_X_SLOT) = vk_permutation_1X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_Y_SLOT) = vk_permutation_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_X_SLOT) = vk_permutation_2X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_Y_SLOT) = vk_permutation_2Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_X_SLOT) = vk_permutation_3X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_Y_SLOT) = vk_permutation_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_X_SLOT) = vk_lookup_table_0X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_Y_SLOT) = vk_lookup_table_0Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_X_SLOT) = vk_lookup_table_1X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_Y_SLOT) = vk_lookup_table_1Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_X_SLOT) = vk_lookup_table_2X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_Y_SLOT) = vk_lookup_table_2Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_X_SLOT) = vk_lookup_table_3X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_Y_SLOT) = vk_lookup_table_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_X_SLOT) = vk_lookup_selector_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_Y_SLOT) = vk_lookup_selector_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_X_SLOT) =
  vk_lookup_table_type_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) =
  vk_lookup_table_type_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) =
  vk_lookup_table_type_Y{2} /\
  mload mlvk VK_RECURSIVE_FLAG_SLOT = uint256_of_bool vk_recursive_flag{2} /\
  to_uint (mload mlvk TRANSCRIPT_STATE_0_SLOT) = 0 /\
  to_uint (mload mlvk TRANSCRIPT_STATE_1_SLOT) = 0 /\
  (Primops.reverted{1} /\ failed{2} \/
  (!Primops.reverted{1} /\
   !failed{2} /\
   to_uint (mload mit PROOF_PUBLIC_INPUT) = _public_input{2} /\
   to_uint (mload mlp PROOF_STATE_POLYS_0_X_SLOT) = _state_poly_0{2}.`1 /\
   to_uint (mload mlp PROOF_STATE_POLYS_0_Y_SLOT) = _state_poly_0{2}.`2 /\
   to_uint (mload mlp PROOF_STATE_POLYS_1_X_SLOT) = _state_poly_1{2}.`1 /\
   to_uint (mload mlp PROOF_STATE_POLYS_1_Y_SLOT) = _state_poly_1{2}.`2 /\
   to_uint (mload mlp PROOF_STATE_POLYS_2_X_SLOT) = _state_poly_2{2}.`1 /\
   to_uint (mload mlp PROOF_STATE_POLYS_2_Y_SLOT) = _state_poly_2{2}.`2 /\
   to_uint (mload mlp PROOF_STATE_POLYS_3_X_SLOT) = _state_poly_3{2}.`1 /\
   to_uint (mload mlp PROOF_STATE_POLYS_3_Y_SLOT) = _state_poly_3{2}.`2 /\
   to_uint (mload mlp PROOF_LOOKUP_S_POLY_X_SLOT) = _lookup_s_poly{2}.`1 /\
   to_uint (mload mlp PROOF_LOOKUP_S_POLY_Y_SLOT) = _lookup_s_poly{2}.`2 /\
   to_uint (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT) =
   _copy_permutation_grand_product{2}.`1 /\
   to_uint (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT) =
   _copy_permutation_grand_product{2}.`2 /\
   to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT) =
   _lookup_grand_product{2}.`1 /\
   to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT) =
   _lookup_grand_product{2}.`2 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT) =
   _quotient_poly_part_0{2}.`1 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT) =
   _quotient_poly_part_0{2}.`2 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT) =
   _quotient_poly_part_1{2}.`1 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT) =
   _quotient_poly_part_1{2}.`2 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT) =
   _quotient_poly_part_2{2}.`1 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT) =
   _quotient_poly_part_2{2}.`2 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT) =
   _quotient_poly_part_3{2}.`1 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT) =
   _quotient_poly_part_3{2}.`2 /\
   to_uint (mload mit PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
   _quotient_poly_opening_at_z{2} /\
   to_uint (mload mit PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
   _state_poly_0_opening_at_z{2} /\
   to_uint (mload mit PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
   _state_poly_1_opening_at_z{2} /\
   to_uint (mload mit PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
   _state_poly_2_opening_at_z{2} /\
   to_uint (mload mit PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
   _state_poly_3_opening_at_z{2} /\
   to_uint (mload mlp PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) =
   _state_poly_3_opening_at_z_omega{2} /\
   to_uint (mload mit PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
   _gate_selector_0_opening_at_z{2} /\
   to_uint (mload mit PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
   _copy_permutation_poly_0_opening_at_z{2} /\
   to_uint (mload mit PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
   _copy_permutation_poly_1_opening_at_z{2} /\
   to_uint (mload mit PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
   _copy_permutation_poly_2_opening_at_z{2} /\
   to_uint
     (mload mit PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   _copy_permutation_grand_product_opening_at_z_omega{2} /\
   to_uint (mload mlp PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) =
   _lookup_t_poly_opening_at_z{2} /\
   to_uint (mload mlp PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) =
   _lookup_selector_poly_opening_at_z{2} /\
   to_uint (mload mlp PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) =
   _lookup_table_type_poly_opening_at_z{2} /\
   to_uint (mload mit PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   _lookup_s_poly_opening_at_z_omega{2} /\
   to_uint (mload mit PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   _lookup_grand_product_opening_at_z_omega{2} /\
   to_uint (mload mlp PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   _lookup_t_poly_opening_at_z_omega{2} /\
   to_uint (mload mit PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
   _linearisation_poly_opening_at_z{2} /\
   to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_X_SLOT) =
   _opening_proof_at_z{2}.`1 /\
   to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_Y_SLOT) =
   _opening_proof_at_z{2}.`2 /\
   to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT) =
   _opening_proof_at_z_omega{2}.`1 /\
   to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT) = _opening_proof_at_z_omega{2}.`2 /\
   to_uint (mload mit STATE_ALPHA_SLOT) = state_alpha{2} /\
   to_uint (mload mit STATE_BETA_SLOT) = state_beta{2} /\
   to_uint (mload mit STATE_BETA_LOOKUP_SLOT) = state_beta_lookup{2} /\
   to_uint (mload mit STATE_GAMMA_SLOT) = state_gamma{2} /\
   to_uint (mload mit STATE_GAMMA_LOOKUP_SLOT) = state_gamma_lookup{2} /\
   to_uint (mload mit STATE_Z_SLOT) = state_z{2} /\
   to_uint (mload mit STATE_Z_IN_DOMAIN_SIZE) = state_z_in_domain{2} /\
   0 <= state_alpha{2} < 2^253 /\ 
   0 <= state_beta{2} < 2^253 /\ 
  0 <= state_beta_lookup{2} < 2^253 /\ 
  0 <= state_gamma{2} < 2^253 /\
  0 <= state_gamma_lookup{2} < 2^253 /\ 
  0 <= state_eta{2} < 2^253 /\ 
  0 <= state_z{2} < 2^253 /\ 
  0 <= state_z_in_domain{2} < Constants.R /\
  0 <= state_v{2} < 2^253 /\ 0 <= state_u{2} < 2^253 /\
   Primops.memory{1} = mit))
).
skip. progress.
case H2. progress. left. progress. progress. right. progress.
rewrite /mit /initializeTranscript_memory_footprint /getTranscriptChallenge_memory_footprint /updateTranscript_memory_footprint /PROOF_PUBLIC_INPUT /PROOF_STATE_POLYS_0_X_SLOT /PROOF_STATE_POLYS_0_Y_SLOT /PROOF_STATE_POLYS_1_Y_SLOT
/PROOF_STATE_POLYS_2_X_SLOT /PROOF_STATE_POLYS_2_Y_SLOT /PROOF_STATE_POLYS_3_X_SLOT /PROOF_STATE_POLYS_3_Y_SLOT
/PROOF_LOOKUP_S_POLY_X_SLOT /PROOF_LOOKUP_S_POLY_Y_SLOT /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT
/PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT
/PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT /PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT
/PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT
/PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT /PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT
/PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT
/PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT 
/PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT
/PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT
/PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT
/PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT
/PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT /PROOF_OPENING_PROOF_AT_Z_X_SLOT /PROOF_OPENING_PROOF_AT_Z_Y_SLOT
/PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT /PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT
/PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT /PROOF_STATE_POLYS_1_X_SLOT
/TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_STATE_1_SLOT /STATE_U_SLOT /TRANSCRIPT_CHALLENGE_SLOT /TRANSCRIPT_DST_BYTE_SLOT. progress.
do 2! (rewrite load_store_diff; try by simplify).
rewrite load_store8_diff_32; try by simplify.
do 2! (rewrite load_store_diff; try by simplify).
rewrite load_store8_diff_32; try by simplify.
rewrite load_store_diff; try by simplify.

seq 1 2:(
  alpha_r = state_alpha{2} /\
  beta_r = state_beta{2} /\
  beta_lookup_r = state_beta_lookup{2} /\
  gamma_r = state_gamma{2} /\
  gamma_lookup_r = state_gamma_lookup{2} /\
  eta_r = state_eta{2} /\
  z_r = state_z{2} /\
  z_in_domain_r = state_z_in_domain{2} /\
  v_r = state_v{2} /\ u_r = state_u{2} /\
  rf = vk_recursive_flag{2} /\
  vk_recursive_flag{2} = false /\
  mod_public_input = _public_input{2} /\
  mod_state_poly_0 = _state_poly_0{2} /\
  mod_state_poly_1 = _state_poly_1{2} /\
  mod_state_poly_2 = _state_poly_2{2} /\
  mod_state_poly_3 = _state_poly_3{2} /\
  mod_copy_permutation_grand_product = _copy_permutation_grand_product{2} /\
  mod_lookup_s_poly = _lookup_s_poly{2} /\
  mod_lookup_grand_product = _lookup_grand_product{2} /\
  mod_quotient_poly_part_0 = _quotient_poly_part_0{2} /\
  mod_quotient_poly_part_1 = _quotient_poly_part_1{2} /\
  mod_quotient_poly_part_2 = _quotient_poly_part_2{2} /\
  mod_quotient_poly_part_3 = _quotient_poly_part_3{2} /\
  mod_state_poly_0_opening_at_z = _state_poly_0_opening_at_z{2} /\
  mod_state_poly_1_opening_at_z = _state_poly_1_opening_at_z{2} /\
  mod_state_poly_2_opening_at_z = _state_poly_2_opening_at_z{2} /\
  mod_state_poly_3_opening_at_z = _state_poly_3_opening_at_z{2} /\
  mod_state_poly_3_opening_at_z_omega = _state_poly_3_opening_at_z_omega{2} /\
  mod_gate_selector_0_opening_at_z = _gate_selector_0_opening_at_z{2} /\
  mod_copy_permutation_poly_0_opening_at_z =
  _copy_permutation_poly_0_opening_at_z{2} /\
  mod_copy_permutation_poly_1_opening_at_z =
  _copy_permutation_poly_1_opening_at_z{2} /\
  mod_copy_permutation_poly_2_opening_at_z =
  _copy_permutation_poly_2_opening_at_z{2} /\
  mod_copy_permutation_grand_product_opening_at_z_omega =
  _copy_permutation_grand_product_opening_at_z_omega{2} /\
  mod_lookup_s_poly_opening_at_z_omega = _lookup_s_poly_opening_at_z_omega{2} /\
  mod_lookup_grand_product_opening_at_z_omega =
  _lookup_grand_product_opening_at_z_omega{2} /\
  mod_lookup_t_poly_opening_at_z = _lookup_t_poly_opening_at_z{2} /\
  mod_lookup_t_poly_opening_at_z_omega = _lookup_t_poly_opening_at_z_omega{2} /\
  mod_lookup_selector_poly_opening_at_z =
  _lookup_selector_poly_opening_at_z{2} /\
  mod_lookup_table_type_poly_opening_at_z =
  _lookup_table_type_poly_opening_at_z{2} /\
  mod_quotient_poly_opening_at_z = _quotient_poly_opening_at_z{2} /\
  mod_linearisation_poly_opening_at_z = _linearisation_poly_opening_at_z{2} /\
  mod_opening_proof_at_z = _opening_proof_at_z{2} /\
  mod_opening_proof_at_z_omega = _opening_proof_at_z_omega{2} /\
  mod_recursive_part_p1 = _recursive_part_p1{2} /\
  mod_recursive_part_p2 = _recursive_part_p2{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_0_X_SLOT) = vk_gate_setup_0X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_0_Y_SLOT) = vk_gate_setup_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_X_SLOT) = vk_gate_setup_1X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_1_Y_SLOT) = vk_gate_setup_1Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_X_SLOT) = vk_gate_setup_2X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_2_Y_SLOT) = vk_gate_setup_2Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_X_SLOT) = vk_gate_setup_3X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_3_Y_SLOT) = vk_gate_setup_3Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_X_SLOT) = vk_gate_setup_4X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_4_Y_SLOT) = vk_gate_setup_4Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_X_SLOT) = vk_gate_setup_5X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_5_Y_SLOT) = vk_gate_setup_5Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_X_SLOT) = vk_gate_setup_6X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_6_Y_SLOT) = vk_gate_setup_6Y{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_X_SLOT) = vk_gate_setup_7X{2} /\
  to_uint (mload mlvk VK_GATE_SETUP_7_Y_SLOT) = vk_gate_setup_7Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_X_SLOT) = vk_gate_selectors_0X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_0_Y_SLOT) = vk_gate_selectors_0Y{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_X_SLOT) = vk_gate_selectors_1X{2} /\
  to_uint (mload mlvk VK_GATE_SELECTORS_1_Y_SLOT) = vk_gate_selectors_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_X_SLOT) = vk_permutation_0X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_0_Y_SLOT) = vk_permutation_0Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_X_SLOT) = vk_permutation_1X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_1_Y_SLOT) = vk_permutation_1Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_X_SLOT) = vk_permutation_2X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_2_Y_SLOT) = vk_permutation_2Y{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_X_SLOT) = vk_permutation_3X{2} /\
  to_uint (mload mlvk VK_PERMUTATION_3_Y_SLOT) = vk_permutation_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_X_SLOT) = vk_lookup_table_0X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_0_Y_SLOT) = vk_lookup_table_0Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_X_SLOT) = vk_lookup_table_1X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_1_Y_SLOT) = vk_lookup_table_1Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_X_SLOT) = vk_lookup_table_2X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_2_Y_SLOT) = vk_lookup_table_2Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_X_SLOT) = vk_lookup_table_3X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_3_Y_SLOT) = vk_lookup_table_3Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_X_SLOT) = vk_lookup_selector_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_SELECTOR_Y_SLOT) = vk_lookup_selector_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_X_SLOT) =
  vk_lookup_table_type_X{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) =
  vk_lookup_table_type_Y{2} /\
  to_uint (mload mlvk VK_LOOKUP_TABLE_TYPE_Y_SLOT) =
  vk_lookup_table_type_Y{2} /\
  mload mlvk VK_RECURSIVE_FLAG_SLOT = uint256_of_bool vk_recursive_flag{2} /\
  to_uint (mload mlvk TRANSCRIPT_STATE_0_SLOT) = 0 /\
  to_uint (mload mlvk TRANSCRIPT_STATE_1_SLOT) = 0 /\
  (Primops.reverted{1} /\ failed{2} \/
  (!Primops.reverted{1} /\ !failed{2} /\
   to_uint (mload mlp PROOF_PUBLIC_INPUT) = _public_input{2} /\
   to_uint (mload mlp PROOF_STATE_POLYS_0_X_SLOT) = _state_poly_0{2}.`1 /\
   to_uint (mload mlp PROOF_STATE_POLYS_0_Y_SLOT) = _state_poly_0{2}.`2 /\
   to_uint (mload mlp PROOF_STATE_POLYS_1_X_SLOT) = _state_poly_1{2}.`1 /\
   to_uint (mload mlp PROOF_STATE_POLYS_1_Y_SLOT) = _state_poly_1{2}.`2 /\
   to_uint (mload mlp PROOF_STATE_POLYS_2_X_SLOT) = _state_poly_2{2}.`1 /\
   to_uint (mload mlp PROOF_STATE_POLYS_2_Y_SLOT) = _state_poly_2{2}.`2 /\
   to_uint (mload mlp PROOF_STATE_POLYS_3_X_SLOT) = _state_poly_3{2}.`1 /\
   to_uint (mload mlp PROOF_STATE_POLYS_3_Y_SLOT) = _state_poly_3{2}.`2 /\
   to_uint (mload mlp PROOF_LOOKUP_S_POLY_X_SLOT) = _lookup_s_poly{2}.`1 /\
   to_uint (mload mlp PROOF_LOOKUP_S_POLY_Y_SLOT) = _lookup_s_poly{2}.`2 /\
   to_uint (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT) =
   _copy_permutation_grand_product{2}.`1 /\
   to_uint (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT) =
   _copy_permutation_grand_product{2}.`2 /\
   to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT) =
   _lookup_grand_product{2}.`1 /\
   to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT) =
   _lookup_grand_product{2}.`2 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT) =
   _quotient_poly_part_0{2}.`1 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT) =
   _quotient_poly_part_0{2}.`2 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT) =
   _quotient_poly_part_1{2}.`1 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT) =
   _quotient_poly_part_1{2}.`2 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT) =
   _quotient_poly_part_2{2}.`1 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT) =
   _quotient_poly_part_2{2}.`2 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT) =
   _quotient_poly_part_3{2}.`1 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT) =
   _quotient_poly_part_3{2}.`2 /\
   to_uint (mload mlp PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) =
   _quotient_poly_opening_at_z{2} /\
   to_uint (mload mlp PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) =
   _state_poly_0_opening_at_z{2} /\
   to_uint (mload mlp PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) =
   _state_poly_1_opening_at_z{2} /\
   to_uint (mload mlp PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) =
   _state_poly_2_opening_at_z{2} /\
   to_uint (mload mlp PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) =
   _state_poly_3_opening_at_z{2} /\
   to_uint (mload mlp PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) =
   _state_poly_3_opening_at_z_omega{2} /\
   to_uint (mload mlp PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) =
   _gate_selector_0_opening_at_z{2} /\
   to_uint (mload mlp PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) =
   _copy_permutation_poly_0_opening_at_z{2} /\
   to_uint (mload mlp PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) =
   _copy_permutation_poly_1_opening_at_z{2} /\
   to_uint (mload mlp PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) =
   _copy_permutation_poly_2_opening_at_z{2} /\
   to_uint
     (mload mlp PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   _copy_permutation_grand_product_opening_at_z_omega{2} /\
   to_uint (mload mlp PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) =
   _lookup_t_poly_opening_at_z{2} /\
   to_uint (mload mlp PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) =
   _lookup_selector_poly_opening_at_z{2} /\
   to_uint (mload mlp PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) =
   _lookup_table_type_poly_opening_at_z{2} /\
   to_uint (mload mlp PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   _lookup_s_poly_opening_at_z_omega{2} /\
   to_uint (mload mlp PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) =
   _lookup_grand_product_opening_at_z_omega{2} /\
   to_uint (mload mlp PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) =
   _lookup_t_poly_opening_at_z_omega{2} /\
   to_uint (mload mlp PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) =
   _linearisation_poly_opening_at_z{2} /\
   to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_X_SLOT) =
   _opening_proof_at_z{2}.`1 /\
   to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_Y_SLOT) =
   _opening_proof_at_z{2}.`2 /\
   to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_OMEGA_X_SLOT) =
   _opening_proof_at_z_omega{2}.`1 /\
   to_uint (mload mlp PROOF_OPENING_PROOF_AT_Z_OMEGA_Y_SLOT) =
   _opening_proof_at_z_omega{2}.`2 /\
  0 <= state_alpha{2} < 2^253 /\ 
  0 <= state_beta{2} < 2^253 /\ 
  0 <= state_beta_lookup{2} < 2^253 /\ 
  0 <= state_gamma{2} < 2^253 /\
  0 <= state_gamma_lookup{2} < 2^253 /\ 
  0 <= state_eta{2} < 2^253 /\ 
  0 <= state_z{2} < 2^253 /\ 
  0 <= state_z_in_domain{2} < Constants.R /\
  0 <= state_v{2} < 2^253 /\ 0 <= state_u{2} < 2^253 /\
  0 <= alpha2{2} < Constants.R /\
  0 <= alpha3{2} < Constants.R /\
  0 <= alpha4{2} < Constants.R /\
  0 <= alpha5{2} < Constants.R /\
  0 <= alpha6{2} < Constants.R /\
  0 <= alpha7{2} < Constants.R /\
  0 <= alpha8{2} < Constants.R /\
  0 <= l0_at_z{2} < Constants.R /\
  0 <= ln_minus_one_at_z{2} < Constants.R /\
  0 <= beta_plus_one{2} < Constants.R /\
  0 <= beta_gamma_plus_gamma{2} < Constants.R /\
  0 <= z_minus_last_omega{2} < Constants.R /\
  exists (v1 v2 v3 v4 v5 v6 v7 v8 : uint256),
  Primops.memory{1} = verifyQuotientEvaluation_memory_footprint mit
  (W256.of_int alpha2{2}) (W256.of_int alpha3{2}) (W256.of_int alpha4{2}) (W256.of_int alpha5{2}) 
  (W256.of_int alpha6{2}) (W256.of_int alpha7{2}) (W256.of_int alpha8{2})
  (W256.of_int l0_at_z{2}) (W256.of_int ln_minus_one_at_z{2})
  (W256.of_int beta_plus_one{2}) (W256.of_int beta_gamma_plus_gamma{2}) (W256.of_int z_minus_last_omega{2})
  v1 v2 v3 v4 v5 v6 v7 v8
))
).
exists* Primops.reverted{1}. elim*=> reverted.
case reverted. progress.
conseq (_ : Primops.reverted{1} /\ failed{2}  ==> Primops.reverted{1} /\ failed{2}).
progress. case H2. by progress. by progress.
progress. left. by progress.
inline VerifyQuotientEvaluation.mid EvaluateLagrangePolyOutOfDomain.EvaluateLagrangePolyOutOfDomain.mid PermutationQuotientContribution.PermutationQuotientContribution.mid LookupQuotientContribution.LookupQuotientContribution.mid Modexp.Modexp.mid.
wp.
call{1} verifyQuotientEvaluation_low_pspec_revert.
skip. simplify. progress.
left. progress.
wp. call (verifyQuotientEvaluation_low_equiv_mid mit
alpha_r 
beta_r 
beta_lookup_r 
gamma_r 
gamma_lookup_r 
z_r 
mod_public_input 
mod_copy_permutation_poly_0_opening_at_z
mod_copy_permutation_poly_1_opening_at_z
mod_copy_permutation_poly_2_opening_at_z
mod_state_poly_0_opening_at_z
mod_state_poly_1_opening_at_z
mod_state_poly_2_opening_at_z
mod_state_poly_3_opening_at_z
mod_lookup_s_poly_opening_at_z_omega
mod_lookup_grand_product_opening_at_z_omega
mod_gate_selector_0_opening_at_z
mod_linearisation_poly_opening_at_z
mod_copy_permutation_grand_product_opening_at_z_omega
z_in_domain_r
mod_quotient_poly_opening_at_z).
skip. progress; case H2; progress.
