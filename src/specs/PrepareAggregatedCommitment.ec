pragma Goals:printall.
require        Constants.
require import EllipticCurve.
require import Field.
require import PointAddIntoDest.
require import PointMulIntoDest.
require import PurePrimops.
require import UInt256.
require import UpdateAggregationChallenge.
require import UpdateAggregationChallenge105.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

module PrepareAggregatedCommitment = {
  proc low(): unit = {
  var aggregationChallenge, firstDCoeff, firstTCoeff, _2, _5, aggregatedOpeningAtZ, _11, _13, _14, _21, _23, _24, _33, _35, _36, _42, _44, _45, _47, copyPermutationCoeff, _51, aggregatedOpeningAtZOmega, _55, _59, u, _66, _67, _68, aggregatedValue;
    aggregationChallenge <- W256.one;
    _2 <@ Primops.mload(QUERIES_AT_Z_0_X_SLOT);
    Primops.mstore(AGGREGATED_AT_Z_X_SLOT, _2); (* <- ! *)
    _5 <@ Primops.mload(QUERIES_AT_Z_0_Y_SLOT);
    Primops.mstore(AGGREGATED_AT_Z_Y_SLOT, _5); (* <- ! *)
    aggregatedOpeningAtZ <@ Primops.mload(PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT);
    PointAddIntoDest.low(AGGREGATED_AT_Z_X_SLOT, QUERIES_AT_Z_1_X_SLOT, AGGREGATED_AT_Z_X_SLOT); (* <- ! *)
    _11 <@ Primops.mload(STATE_V_SLOT);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _11 R_MOD);
    _13 <@ Primops.mload(PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT);
    _14 <- (PurePrimops.mulmod aggregationChallenge _13 R_MOD);
    aggregatedOpeningAtZ <- (PurePrimops.addmod aggregatedOpeningAtZ _14 R_MOD);
    
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(PROOF_STATE_POLYS_0_X_SLOT, PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ); (* <- *)
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(PROOF_STATE_POLYS_1_X_SLOT, PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ); (* <- *)
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(PROOF_STATE_POLYS_2_X_SLOT, PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ); (* <- *)
    _21 <@ Primops.mload(STATE_V_SLOT);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _21 R_MOD);
    firstDCoeff <- aggregationChallenge;
    _23 <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    _24 <- (PurePrimops.mulmod aggregationChallenge _23 R_MOD);
    aggregatedOpeningAtZ <- (PurePrimops.addmod aggregatedOpeningAtZ _24 R_MOD);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_GATE_SELECTORS_0_X_SLOT, PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ); (* <- *)
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_PERMUTATION_0_X_SLOT, PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ); (* <- *)
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_PERMUTATION_1_X_SLOT, PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ); (* <- *)
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_PERMUTATION_2_X_SLOT, PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ); (* <- *)
    _33 <@ Primops.mload(STATE_V_SLOT);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _33 R_MOD);
    firstTCoeff <- aggregationChallenge;
    _35 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT);
    _36 <- (PurePrimops.mulmod aggregationChallenge _35 R_MOD);
    aggregatedOpeningAtZ <- (PurePrimops.addmod aggregatedOpeningAtZ _36 R_MOD);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_LOOKUP_SELECTOR_X_SLOT, PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ); (* <- *)
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_LOOKUP_TABLE_TYPE_X_SLOT, PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ); (* <- *)
    Primops.mstore(AGGREGATED_OPENING_AT_Z_SLOT, aggregatedOpeningAtZ); (* <- *)
    _42 <@ Primops.mload(STATE_V_SLOT);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _42 R_MOD);
    _44 <@ Primops.mload(STATE_U_SLOT);
    _45 <- (PurePrimops.mulmod aggregationChallenge _44 R_MOD);
    _47 <@ Primops.mload(COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF);
    copyPermutationCoeff <- (PurePrimops.addmod _47 _45 R_MOD);
    PointMulIntoDest.low(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT, copyPermutationCoeff, AGGREGATED_AT_Z_OMEGA_X_SLOT); (* <- *)
    _51 <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    aggregatedOpeningAtZOmega <- (PurePrimops.mulmod _51 aggregationChallenge R_MOD); 
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(PROOF_STATE_POLYS_3_X_SLOT, PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT, firstDCoeff, aggregationChallenge, aggregatedOpeningAtZOmega); (* <- *)
    _55 <@ Primops.mload(LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF);
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(PROOF_LOOKUP_S_POLY_X_SLOT, PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT, _55, aggregationChallenge, aggregatedOpeningAtZOmega); (* <- *)
    _59 <@ Primops.mload(LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF);
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT, PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT, _59, aggregationChallenge, aggregatedOpeningAtZOmega); (* <- *)
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(QUERIES_T_POLY_AGGREGATED_X_SLOT, PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT, firstTCoeff, aggregationChallenge, aggregatedOpeningAtZOmega); (* <- *)
    Primops.mstore(AGGREGATED_OPENING_AT_Z_OMEGA_SLOT, aggregatedOpeningAtZOmega); (* <- *)
    u <@ Primops.mload(STATE_U_SLOT);
    PointAddIntoDest.low(AGGREGATED_AT_Z_X_SLOT, AGGREGATED_AT_Z_OMEGA_X_SLOT, PAIRING_PAIR_WITH_GENERATOR_X_SLOT); (* <- *)
    _66 <@ Primops.mload(AGGREGATED_OPENING_AT_Z_SLOT);
    _67 <@ Primops.mload(AGGREGATED_OPENING_AT_Z_OMEGA_SLOT);
    _68 <- (PurePrimops.mulmod _67 u R_MOD);
    aggregatedValue <- (PurePrimops.addmod _68 _66 R_MOD);
    Primops.mstore(PAIRING_BUFFER_POINT_X_SLOT, W256.one); (* <- *)
    Primops.mstore(PAIRING_BUFFER_POINT_Y_SLOT, W256.of_int 2); (* <- *)
    PointMulIntoDest.low(PAIRING_BUFFER_POINT_X_SLOT, aggregatedValue, PAIRING_BUFFER_POINT_X_SLOT); (* <- *)
  }

  proc mid(queriesAtZ0Slot : (int * int), proofQuotientPolyOpeningAtZSlot : int, queriesAtZ1Slot : int * int, v_challenge : int, proofLinearisationPolyOpeningAtZSlot : int, proofStatePolys0XSlot : int * int, proofStatePolys0OpeningAtZSlot : int, proofStatePolys1Slot : int * int, proofStatePolys1OpeningAtZSlot : int, proofStatePolys2Slot : int * int, proofStatePolys2OpeningAtZSlot : int, proofStatePolys3OpeningAtZSlot : int, vkGateSelectors0Slot : int * int, proofGateSelectors0OpeningAtZSlot : int, vkPermutation0Slot : int * int, proofCopyPermutationPolys0OpeningAtZSlot : int, vkPermutation1Slot : int * int, proofCopyPermutationPolys1OpeningAtZSlot : int, vkPermutation2Slot : int * int, proofCopyPermutationPolys2OpeningAtZSlot : int, proofLookupTPolyOpeningAtZSlot : int, vkLookupSelectorSlot : int * int, proofLookupSelectorPolyOpeningAtZSlot : int, vkLookupTableTypeSlot : int * int, proofLookupTableTypePolyOpeningAtZSlot : int, copyPermutationFirstAggregatedCommitmentCoeff : int, u_challenge : int, proofCopyPermutationGrandProductSlot : int * int, proofCopyPermutationGrandProductOpeningAtZOmegaSlot : int, proofStatePolys3Slot : int * int, proofStatePolys3OpeningAtZOmegaSlot : int, aggregatedAtZOmegaSlot : int * int, proofLookupSPolySlot : int * int, proofLookupSPolyOpeningAtZOmegaSlot : int, lookupSFirstAggregatedCommitmentCoeff : int, proofLookupGrandProductSlot : int * int, proofLookupGrandProductOpeningAtZOmegaSlot : int, lookupGrandProductFirstAggregatedCommitmentCoeff : int, queriesTPolyAggregatedSlot : int * int, proofLookupTPolyOpeningAtZOmegaSlot : int) : ((int * int) * int * (int * int) * (int * int) * (int * int)) option = {
      var aggregationChallenge, aggregatedAtZSlot, aggregatedOpeningAtZ, mAggregatedAtZSlot, mUACRes, firstDCoeff, firstTCoeff, aggregatedOpeningAtZSlot, copyPermutationCoeff, mPMID, aggregatedOpeningAtZOmega, mUAC105, pairingPairWithGeneratorSlot, aggregatedValue, mPairingPairWithGeneratorSlot, pairingBufferPointSlot, mPairingBufferPointSlot, result;
      var failed : bool;

      failed <- false;
    
      aggregatedAtZSlot <- queriesAtZ0Slot;
      aggregatedOpeningAtZ <- proofQuotientPolyOpeningAtZSlot;
    
      mAggregatedAtZSlot <@ PointAddIntoDest.mid(aggregatedAtZSlot.`1, aggregatedAtZSlot.`2, queriesAtZ1Slot.`1, queriesAtZ1Slot.`2);
      failed <- failed \/ is_none mAggregatedAtZSlot;
      aggregatedAtZSlot <- odflt (0,0) mAggregatedAtZSlot;

      aggregationChallenge <- v_challenge %% Constants.R;
      aggregatedOpeningAtZ <- (aggregatedOpeningAtZ + aggregationChallenge * proofLinearisationPolyOpeningAtZSlot) %% Constants.R;

      mUACRes <@ UpdateAggregationChallenge.mid(proofStatePolys0XSlot, proofStatePolys0OpeningAtZSlot, aggregationChallenge, aggregatedOpeningAtZ, v_challenge, aggregatedAtZSlot);
      failed <- failed \/ is_none mUACRes;
    (aggregationChallenge, aggregatedOpeningAtZ, aggregatedAtZSlot) <- odflt (0,0,(0,0)) mUACRes;

      mUACRes <@ UpdateAggregationChallenge.mid(proofStatePolys1Slot, proofStatePolys1OpeningAtZSlot, aggregationChallenge, aggregatedOpeningAtZ, v_challenge, aggregatedAtZSlot);
      failed <- failed \/ is_none mUACRes;
    (aggregationChallenge, aggregatedOpeningAtZ, aggregatedAtZSlot) <- odflt (0,0,(0,0)) mUACRes;

      mUACRes <@ UpdateAggregationChallenge.mid(proofStatePolys2Slot, proofStatePolys2OpeningAtZSlot, aggregationChallenge, aggregatedOpeningAtZ, v_challenge, aggregatedAtZSlot);
      failed <- failed \/ is_none mUACRes;
    (aggregationChallenge, aggregatedOpeningAtZ, aggregatedAtZSlot) <- odflt (0,0,(0,0)) mUACRes;

      aggregationChallenge <- aggregationChallenge * v_challenge %% Constants.R;
    
      firstDCoeff <- aggregationChallenge;

      aggregatedOpeningAtZ <- (aggregatedOpeningAtZ + aggregationChallenge * proofStatePolys3OpeningAtZSlot) %% Constants.R;

      mUACRes <@ UpdateAggregationChallenge.mid(vkGateSelectors0Slot, proofGateSelectors0OpeningAtZSlot, aggregationChallenge, aggregatedOpeningAtZ, v_challenge, aggregatedAtZSlot);
      failed <- failed \/ is_none mUACRes;
    (aggregationChallenge, aggregatedOpeningAtZ, aggregatedAtZSlot) <- odflt (0,0,(0,0)) mUACRes;

    mUACRes <@ UpdateAggregationChallenge.mid(vkPermutation0Slot, proofCopyPermutationPolys0OpeningAtZSlot, aggregationChallenge, aggregatedOpeningAtZ, v_challenge, aggregatedAtZSlot);
      failed <- failed \/ is_none mUACRes;
    (aggregationChallenge, aggregatedOpeningAtZ, aggregatedAtZSlot) <- odflt (0,0,(0,0)) mUACRes;

      mUACRes <@ UpdateAggregationChallenge.mid(vkPermutation1Slot, proofCopyPermutationPolys1OpeningAtZSlot, aggregationChallenge, aggregatedOpeningAtZ, v_challenge, aggregatedAtZSlot);
      failed <- failed \/ is_none mUACRes;
    (aggregationChallenge, aggregatedOpeningAtZ, aggregatedAtZSlot) <- odflt (0,0,(0,0)) mUACRes;

      mUACRes <@ UpdateAggregationChallenge.mid(vkPermutation2Slot, proofCopyPermutationPolys2OpeningAtZSlot, aggregationChallenge, aggregatedOpeningAtZ, v_challenge, aggregatedAtZSlot);
      failed <- failed \/ is_none mUACRes;
    (aggregationChallenge, aggregatedOpeningAtZ, aggregatedAtZSlot) <- odflt (0,0,(0,0)) mUACRes;

      aggregationChallenge <- v_challenge * aggregationChallenge %% Constants.R;
    
      firstTCoeff <- aggregationChallenge;

      aggregatedOpeningAtZ <- (aggregatedOpeningAtZ + aggregationChallenge * proofLookupTPolyOpeningAtZSlot) %% Constants.R;

      mUACRes <@ UpdateAggregationChallenge.mid(vkLookupSelectorSlot, proofLookupSelectorPolyOpeningAtZSlot, aggregationChallenge, aggregatedOpeningAtZ, v_challenge, aggregatedAtZSlot);
      failed <- failed \/ is_none mUACRes;
    (aggregationChallenge, aggregatedOpeningAtZ, aggregatedAtZSlot) <- odflt (0,0,(0,0)) mUACRes;

      mUACRes <@ UpdateAggregationChallenge.mid(vkLookupTableTypeSlot, proofLookupTableTypePolyOpeningAtZSlot, aggregationChallenge, aggregatedOpeningAtZ, v_challenge, aggregatedAtZSlot);
      failed <- failed \/ is_none mUACRes;
    (aggregationChallenge, aggregatedOpeningAtZ, aggregatedAtZSlot) <- odflt (0,0,(0,0)) mUACRes;

    aggregatedOpeningAtZSlot <- aggregatedOpeningAtZ;

      aggregationChallenge <- aggregationChallenge * v_challenge %% Constants.R;

      copyPermutationCoeff <- (copyPermutationFirstAggregatedCommitmentCoeff + aggregationChallenge * u_challenge) %% Constants.R;
    
      mPMID <@ PointMulIntoDest.mid(proofCopyPermutationGrandProductSlot.`1, proofCopyPermutationGrandProductSlot.`2, copyPermutationCoeff);
      failed <- failed \/ is_none mPMID;
      aggregatedAtZOmegaSlot <- odflt (0,0) mPMID;

      aggregatedOpeningAtZOmega <- proofCopyPermutationGrandProductOpeningAtZOmegaSlot * aggregationChallenge %% Constants.R;

      mUAC105 <@ UpdateAggregationChallenge_105.mid(proofStatePolys3Slot, proofStatePolys3OpeningAtZOmegaSlot, firstDCoeff, aggregationChallenge, aggregatedOpeningAtZOmega, v_challenge, u_challenge, aggregatedAtZOmegaSlot);
      failed <- failed \/ is_none mUAC105;
    (aggregationChallenge, aggregatedOpeningAtZOmega, aggregatedAtZOmegaSlot) <- odflt (0,0, (0,0)) mUAC105;

      mUAC105 <@ UpdateAggregationChallenge_105.mid(proofLookupSPolySlot, proofLookupSPolyOpeningAtZOmegaSlot, lookupSFirstAggregatedCommitmentCoeff, aggregationChallenge, aggregatedOpeningAtZOmega, v_challenge, u_challenge, aggregatedAtZOmegaSlot);
      failed <- failed \/ is_none mUAC105;
    (aggregationChallenge, aggregatedOpeningAtZOmega, aggregatedAtZOmegaSlot) <- odflt (0,0, (0,0)) mUAC105;

      mUAC105 <@ UpdateAggregationChallenge_105.mid(proofLookupGrandProductSlot, proofLookupGrandProductOpeningAtZOmegaSlot, lookupGrandProductFirstAggregatedCommitmentCoeff, aggregationChallenge, aggregatedOpeningAtZOmega, v_challenge, u_challenge, aggregatedAtZOmegaSlot);
      failed <- failed \/ is_none mUAC105;
    (aggregationChallenge, aggregatedOpeningAtZOmega, aggregatedAtZOmegaSlot) <- odflt (0,0, (0,0)) mUAC105;

    mUAC105 <@ UpdateAggregationChallenge_105.mid(queriesTPolyAggregatedSlot, proofLookupTPolyOpeningAtZOmegaSlot, firstTCoeff, aggregationChallenge, aggregatedOpeningAtZOmega, v_challenge, u_challenge, aggregatedAtZOmegaSlot);
      failed <- failed \/ is_none mUAC105;
      (aggregationChallenge, aggregatedOpeningAtZOmega, aggregatedAtZOmegaSlot) <- odflt (0,0, (0,0)) mUAC105;

        mPairingPairWithGeneratorSlot <@ PointAddIntoDest.mid(aggregatedAtZSlot.`1, aggregatedAtZSlot.`2, aggregatedAtZOmegaSlot.`1, aggregatedAtZOmegaSlot.`2);
        failed <- failed \/ is_none mPairingPairWithGeneratorSlot;
        pairingPairWithGeneratorSlot <- odflt (0,0) mPairingPairWithGeneratorSlot;
      
        aggregatedValue <- (aggregatedOpeningAtZOmega * u_challenge + aggregatedOpeningAtZ) %% Constants.R;
      
        mPairingBufferPointSlot <@ PointMulIntoDest.mid(1, 2, aggregatedValue);
        failed <- failed \/ is_none mPairingBufferPointSlot;
        pairingBufferPointSlot <- odflt (0,0) mPairingBufferPointSlot;

        if (failed) {
          result <- None;
        } else {
          result <- Some (aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, pairingPairWithGeneratorSlot, pairingBufferPointSlot);
        }

        return result;
    
  }
}.

lemma prepareAggregatedCommitment_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_prepareAggregatedCommitment ~ PrepareAggregatedCommitment.low:
      ={arg, glob PrepareAggregatedCommitment} ==>
      ={res, glob PrepareAggregatedCommitment}
    ].
    proof.
      proc.
      seq 11 5: (#pre /\ _3{1} = AGGREGATED_AT_Z_X_SLOT /\ usr_aggregationChallenge{1} = aggregationChallenge{2}). inline*. wp. skip. by progress.
      seq 5 2: (#pre /\ usr_aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2}). inline Primops.mload. sp. call pointAddIntoDest_extracted_equiv_low. skip. by progress.
      seq 22 8: (#pre /\ _9{1} = R_MOD /\ _10{1} = STATE_V_SLOT). wp. do 3! (call updateAggregationChallenge_extracted_equiv_low; wp). inline Primops.mload. wp. skip. rewrite /Constants.R. by progress.
      seq 25 10: (#pre /\ usr_firstDCoeff{1} = firstDCoeff{2}). wp. do 4! (call updateAggregationChallenge_extracted_equiv_low; wp). inline*. wp. skip. by progress.
      seq 17 8: (#pre /\ usr_firstTCoeff{1} = firstTCoeff{2} ). wp. do 2! (call updateAggregationChallenge_extracted_equiv_low; wp). inline*. wp. skip. by progress.
      seq 16 8: (#pre /\ _41{1} = AGGREGATED_OPENING_AT_Z_SLOT /\ _43{1} = STATE_U_SLOT /\_48{1} = AGGREGATED_AT_Z_OMEGA_X_SLOT). call pointMulIntoDest_extracted_equiv_low. inline*. wp. skip. by progress.
      seq 26 8: (#pre /\ usr_aggregatedOpeningAtZOmega{1} = aggregatedOpeningAtZOmega{2}). wp. inline Primops.mload. do 4! (call updateAggregationChallenge_105_extracted_equiv_low; wp). skip. by progress.
      call pointMulIntoDest_extracted_equiv_low.
      inline Primops.mstore Primops.mload. wp.
      call pointAddIntoDest_extracted_equiv_low.
      wp. skip. by progress.
    qed.
    
op prepareAggregatedCommitment_memory_footprint (mem_0 : mem) (aggregatedAtZSlot_rep : int * int) (aggregatedOpeningAtZSlot_rep : uint256) (aggregatedAtZOmegaXSlot_rep : int * int) (pairingPairWithGeneratorSlot_rep : int * int) (pairingBufferPointSlot_rep : int * int) (v1 v2 v3 v4 : uint256) : mem =
let mem_1 = store mem_0 AGGREGATED_AT_Z_X_SLOT (W256.of_int aggregatedAtZSlot_rep.`1) in
let mem_2 = store mem_1 AGGREGATED_AT_Z_Y_SLOT (W256.of_int aggregatedAtZSlot_rep.`2) in
let mem_3 = store mem_2 AGGREGATED_OPENING_AT_Z_SLOT aggregatedOpeningAtZSlot_rep in
let mem_4 = store mem_3 AGGREGATED_AT_Z_OMEGA_X_SLOT (W256.of_int aggregatedAtZOmegaXSlot_rep.`1) in
let mem_5 = store mem_4 AGGREGATED_AT_Z_OMEGA_Y_SLOT (W256.of_int aggregatedAtZOmegaXSlot_rep.`2) in
let mem_6 = store mem_5 PAIRING_PAIR_WITH_GENERATOR_X_SLOT (W256.of_int pairingPairWithGeneratorSlot_rep.`1) in
let mem_7 = store mem_6 PAIRING_PAIR_WITH_GENERATOR_Y_SLOT (W256.of_int pairingPairWithGeneratorSlot_rep.`2) in
let mem_8 = store mem_7 PAIRING_BUFFER_POINT_X_SLOT (W256.of_int pairingBufferPointSlot_rep.`1) in
let mem_9 = store mem_8 PAIRING_BUFFER_POINT_Y_SLOT (W256.of_int pairingBufferPointSlot_rep.`2) in
  store (store (store (store mem_9 W256.zero v1) (W256.of_int 32) v2) (W256.of_int 64) v3) (W256.of_int 96) v4.

pred pointInField (pnt : int * int) = 0 <= pnt.`1 < FieldQ.p /\ 0 <= pnt.`2 < FieldQ.p.
(* pred isOpening (opening : int) = 0 <= opening < FieldR.p. *)

pred prepareAggregatedCommitment_mem_inv (mem0 : mem) (queriesAtZ0Slot : (int * int)) (proofQuotientPolyOpeningAtZSlot : int) (queriesAtZ1Slot : int * int) (v_challenge : int) (proofLinearisationPolyOpeningAtZSlot : int) (proofStatePolys0XSlot : int * int) (proofStatePolys0OpeningAtZSlot : int) (proofStatePolys1Slot : int * int) (proofStatePolys1OpeningAtZSlot : int) (proofStatePolys2Slot : int * int) (proofStatePolys2OpeningAtZSlot : int) (proofStatePolys3OpeningAtZSlot : int) (vkGateSelectors0Slot : int * int) (proofGateSelectors0OpeningAtZSlot : int) (vkPermutation0Slot : int * int) (proofCopyPermutationPolys0OpeningAtZSlot : int) (vkPermutation1Slot : int * int) (proofCopyPermutationPolys1OpeningAtZSlot : int) (vkPermutation2Slot : int * int) (proofCopyPermutationPolys2OpeningAtZSlot : int) (proofLookupTPolyOpeningAtZSlot : int) (vkLookupSelectorSlot : int * int) (proofLookupSelectorPolyOpeningAtZSlot : int) (vkLookupTableTypeSlot : int * int) (proofLookupTableTypePolyOpeningAtZSlot : int) (copyPermutationFirstAggregatedCommitmentCoeff : int) (u_challenge : int) (proofCopyPermutationGrandProductSlot : int * int) (proofCopyPermutationGrandProductOpeningAtZOmegaSlot : int) (proofStatePolys3Slot : int * int) (proofStatePolys3OpeningAtZOmegaSlot : int) (aggregatedAtZOmegaSlot : int * int) (proofLookupSPolySlot : int * int) (proofLookupSPolyOpeningAtZOmegaSlot : int) (lookupSFirstAggregatedCommitmentCoeff : int) (proofLookupGrandProductSlot : int * int) (proofLookupGrandProductOpeningAtZOmegaSlot : int) (lookupGrandProductFirstAggregatedCommitmentCoeff : int) (queriesTPolyAggregatedSlot : int * int) (proofLookupTPolyOpeningAtZOmegaSlot : int) =
  pointInField queriesAtZ0Slot /\
  pointInField queriesAtZ1Slot /\
  pointInField proofStatePolys0XSlot /\
  pointInField proofStatePolys1Slot /\
  pointInField proofStatePolys2Slot /\
  pointInField vkGateSelectors0Slot /\
  pointInField vkPermutation0Slot /\
  pointInField vkPermutation1Slot /\
  pointInField vkPermutation2Slot /\
  pointInField vkLookupSelectorSlot /\
  pointInField vkLookupTableTypeSlot /\
  pointInField proofCopyPermutationGrandProductSlot /\
  pointInField proofStatePolys3Slot /\
  pointInField aggregatedAtZOmegaSlot /\
  pointInField proofLookupSPolySlot /\
  pointInField proofLookupGrandProductSlot /\
  pointInField queriesTPolyAggregatedSlot /\
  (* isOpening proofQuotientPolyOpeningAtZSlot /\ *)
  (* isOpening proofLinearisationPolyOpeningAtZSlot /\ *)
  (* isOpening proofStatePolys0OpeningAtZSlot /\ *)
  (* isOpening proofStatePolys3OpeningAtZSlot /\ *)
  (* isOpening proofGateSelectors0OpeningAtZSlot /\ *)
  (* isOpening proofCopyPermutationPolys0OpeningAtZSlot /\ *)
  (* isOpening proofCopyPermutationPolys1OpeningAtZSlot /\ *)
  (* isOpening proofCopyPermutationPolys2OpeningAtZSlot /\ *)
  (* isOpening proofLookupTPolyOpeningAtZSlot /\ *)
  (* isOpening proofLookupSelectorPolyOpeningAtZSlot /\ *)
  (* isOpening proofLookupTableTypePolyOpeningAtZSlot /\ *)
  (* isOpening proofCopyPermutationGrandProductOpeningAtZOmegaSlot /\ *)
  (* isOpening proofStatePolys3OpeningAtZOmegaSlot /\ *)
  (* isOpening proofLookupSPolyOpeningAtZOmegaSlot /\ *)
  (* isOpening proofLookupGrandProductOpeningAtZOmegaSlot /\ *)
  (* isOpening proofLookupTPolyOpeningAtZOmegaSlot /\ *)
  (* 0 <= v_challenge < Constants.R /\ *)
  queriesAtZ0Slot.`1 = W256.to_uint (load mem0 QUERIES_AT_Z_0_X_SLOT) /\
  queriesAtZ0Slot.`2 = W256.to_uint (load mem0 QUERIES_AT_Z_0_Y_SLOT) /\
  proofQuotientPolyOpeningAtZSlot = W256.to_uint (load mem0 PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT) /\
  queriesAtZ1Slot.`1 = W256.to_uint (load mem0 QUERIES_AT_Z_1_X_SLOT) /\
  queriesAtZ1Slot.`2 = W256.to_uint (load mem0 QUERIES_AT_Z_1_Y_SLOT) /\
  v_challenge = W256.to_uint (load mem0 STATE_V_SLOT) /\
  proofLinearisationPolyOpeningAtZSlot = W256.to_uint (load mem0 PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT) /\
  proofStatePolys0XSlot.`1 = W256.to_uint (load mem0 PROOF_STATE_POLYS_0_X_SLOT) /\
  proofStatePolys0XSlot.`2 = W256.to_uint (load mem0 PROOF_STATE_POLYS_0_Y_SLOT) /\
  proofStatePolys0OpeningAtZSlot = W256.to_uint (load mem0 PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) /\
  proofStatePolys1Slot.`1 = W256.to_uint (load mem0 PROOF_STATE_POLYS_1_X_SLOT) /\
  proofStatePolys1Slot.`2 = W256.to_uint (load mem0 PROOF_STATE_POLYS_1_Y_SLOT) /\
  proofStatePolys1OpeningAtZSlot = W256.to_uint (load mem0 PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) /\
  proofStatePolys2Slot.`1 = W256.to_uint (load mem0 PROOF_STATE_POLYS_2_X_SLOT) /\
  proofStatePolys2Slot.`2 = W256.to_uint (load mem0 PROOF_STATE_POLYS_2_Y_SLOT) /\
  proofStatePolys2OpeningAtZSlot = W256.to_uint (load mem0 PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) /\
  proofStatePolys3OpeningAtZSlot = W256.to_uint (load mem0 PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) /\
  vkGateSelectors0Slot.`1 = W256.to_uint (load mem0 VK_GATE_SELECTORS_0_X_SLOT) /\
  vkGateSelectors0Slot.`2 = W256.to_uint (load mem0 VK_GATE_SELECTORS_0_Y_SLOT) /\
  proofGateSelectors0OpeningAtZSlot = W256.to_uint (load mem0 PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
  vkPermutation0Slot.`1 = W256.to_uint (load mem0 VK_PERMUTATION_0_X_SLOT) /\
  vkPermutation0Slot.`2 = W256.to_uint (load mem0 VK_PERMUTATION_0_Y_SLOT) /\
  proofCopyPermutationPolys0OpeningAtZSlot = W256.to_uint (load mem0 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) /\
  vkPermutation1Slot.`1 = W256.to_uint (load mem0 VK_PERMUTATION_1_X_SLOT) /\
  vkPermutation1Slot.`2 = W256.to_uint (load mem0 VK_PERMUTATION_1_Y_SLOT) /\
  proofCopyPermutationPolys1OpeningAtZSlot = W256.to_uint (load mem0 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) /\
  vkPermutation2Slot.`1 = W256.to_uint (load mem0 VK_PERMUTATION_2_X_SLOT) /\
  vkPermutation2Slot.`2 = W256.to_uint (load mem0 VK_PERMUTATION_2_Y_SLOT) /\
  proofCopyPermutationPolys2OpeningAtZSlot = W256.to_uint (load mem0 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) /\
  proofLookupTPolyOpeningAtZSlot = W256.to_uint (load mem0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) /\
  vkLookupSelectorSlot.`1 = W256.to_uint (load mem0 VK_LOOKUP_SELECTOR_X_SLOT) /\
  vkLookupSelectorSlot.`2 = W256.to_uint (load mem0 VK_LOOKUP_SELECTOR_Y_SLOT) /\
  proofLookupSelectorPolyOpeningAtZSlot = W256.to_uint (load mem0 PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) /\
  vkLookupTableTypeSlot.`1 = W256.to_uint (load mem0 VK_LOOKUP_TABLE_TYPE_X_SLOT) /\
  vkLookupTableTypeSlot.`2 = W256.to_uint (load mem0 VK_LOOKUP_TABLE_TYPE_Y_SLOT) /\
  proofLookupTableTypePolyOpeningAtZSlot = W256.to_uint (load mem0 PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) /\
  copyPermutationFirstAggregatedCommitmentCoeff = W256.to_uint (load mem0 COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF) /\
  u_challenge = W256.to_uint (load mem0 STATE_U_SLOT) /\
  proofCopyPermutationGrandProductSlot.`1 = W256.to_uint (load mem0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT) /\
  proofCopyPermutationGrandProductSlot.`2 = W256.to_uint (load mem0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_Y_SLOT) /\
  proofCopyPermutationGrandProductOpeningAtZOmegaSlot = W256.to_uint (load mem0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
  proofStatePolys3Slot.`1 = W256.to_uint (load mem0 PROOF_STATE_POLYS_3_X_SLOT) /\
  proofStatePolys3Slot.`2 = W256.to_uint (load mem0 PROOF_STATE_POLYS_3_Y_SLOT) /\
  proofStatePolys3OpeningAtZOmegaSlot = W256.to_uint (load mem0 PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
  aggregatedAtZOmegaSlot.`1 = W256.to_uint (load mem0 AGGREGATED_AT_Z_OMEGA_X_SLOT) /\
  aggregatedAtZOmegaSlot.`2 = W256.to_uint (load mem0 AGGREGATED_AT_Z_OMEGA_Y_SLOT) /\
  proofLookupSPolySlot.`1 = W256.to_uint (load mem0 PROOF_LOOKUP_S_POLY_X_SLOT) /\
  proofLookupSPolySlot.`2 = W256.to_uint (load mem0 PROOF_LOOKUP_S_POLY_Y_SLOT) /\
  proofLookupSPolyOpeningAtZOmegaSlot = W256.to_uint (load mem0 PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT) /\
  lookupSFirstAggregatedCommitmentCoeff = W256.to_uint (load mem0 LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF) /\
  proofLookupGrandProductSlot.`1 = W256.to_uint (load mem0 PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT) /\
  proofLookupGrandProductSlot.`2 = W256.to_uint (load mem0 PROOF_LOOKUP_GRAND_PRODUCT_Y_SLOT) /\
  proofLookupGrandProductOpeningAtZOmegaSlot = W256.to_uint (load mem0 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
  lookupGrandProductFirstAggregatedCommitmentCoeff = W256.to_uint (load mem0 LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF) /\
  queriesTPolyAggregatedSlot.`1 = W256.to_uint (load mem0 QUERIES_T_POLY_AGGREGATED_X_SLOT) /\
  queriesTPolyAggregatedSlot.`2 = W256.to_uint (load mem0 QUERIES_T_POLY_AGGREGATED_Y_SLOT) /\
  proofLookupTPolyOpeningAtZOmegaSlot = W256.to_uint (load mem0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT).

lemma prepareAggregatedCommitment_low_equiv_mid  (mem0 : mem) :
    equiv [
      PrepareAggregatedCommitment.low ~ PrepareAggregatedCommitment.mid:
      !Primops.reverted{1} /\
      Primops.memory{1} = mem0 /\
      prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2} proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2} proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2} proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2} proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2} proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2} vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2} vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2} vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2} vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2} proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2} proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2} proofLookupTableTypePolyOpeningAtZSlot{2} copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2} proofCopyPermutationGrandProductSlot{2} proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2} proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2} aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2} proofLookupSPolyOpeningAtZOmegaSlot{2} lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2} proofLookupGrandProductOpeningAtZOmegaSlot{2} lookupGrandProductFirstAggregatedCommitmentCoeff{2} queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2}
        ==>
        (Primops.reverted{1} /\ res{2} = None) \/
        (
          !Primops.reverted{2} /\
          exists aggregatedAtZSlot aggregatedOpeningAtZSlot aggregatedAtZOmegaXSlot pairingPairWithGeneratorSlot pairingBufferPointSlot v1 v2 v3 v4,
          res{2} = Some (aggregatedAtZSlot, W256.to_uint aggregatedOpeningAtZSlot, aggregatedAtZOmegaXSlot, pairingPairWithGeneratorSlot, pairingBufferPointSlot) /\
          Primops.memory{1} = prepareAggregatedCommitment_memory_footprint mem0 aggregatedAtZSlot aggregatedOpeningAtZSlot aggregatedAtZOmegaXSlot pairingPairWithGeneratorSlot pairingBufferPointSlot v1 v2 v3 v4
        )
      ]. proc.
          seq 6 3 :
      (
        !Primops.reverted{1} /\
        Primops.memory{1} = store (store mem0 AGGREGATED_AT_Z_X_SLOT (W256.of_int queriesAtZ0Slot{2}.`1)) AGGREGATED_AT_Z_Y_SLOT (W256.of_int queriesAtZ0Slot{2}.`2) /\
        prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2} proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2} proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2} proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2} proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2} proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2} vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2} vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2} vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2} vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2} proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2} proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2} proofLookupTableTypePolyOpeningAtZSlot{2} copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2} proofCopyPermutationGrandProductSlot{2} proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2} proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2} aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2} proofLookupSPolyOpeningAtZOmegaSlot{2} lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2} proofLookupGrandProductOpeningAtZOmegaSlot{2} lookupGrandProductFirstAggregatedCommitmentCoeff{2} queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
        aggregationChallenge{1} = W256.one /\
        !failed{2} /\ aggregatedAtZSlot{2} = queriesAtZ0Slot{2} /\ W256.to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2}
      ). inline*. sp. skip. progress. congr. congr. prover timeout=10. smt (@W256). rewrite load_store_diff /QUERIES_AT_Z_0_Y_SLOT /AGGREGATED_AT_Z_X_SLOT. progress. progress. rewrite -/QUERIES_AT_Z_0_Y_SLOT. smt (@W256).

          rewrite load_store_diff.
          rewrite /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_Y_SLOT. progress.
          rewrite /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_Y_SLOT. progress.

          rewrite load_store_diff.
          rewrite /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT. progress.
          rewrite /PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT. progress.

          smt ().
      
          exists* Primops.memory{1}, aggregatedAtZSlot{2}, queriesAtZ1Slot{2}.
          elim*=> mem1 aggregatedAtZSlot1 queriesAtZ1Slot1.
          seq 1 3 :
      (
        (Primops.reverted{1} /\ failed{2}) \/
        (!Primops.reverted{1} /\ !failed{2} /\
          prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2} proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2} proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2} proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2} proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2} proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2} vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2} vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2} vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2} vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2} proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2} proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2} proofLookupTableTypePolyOpeningAtZSlot{2} copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2} proofCopyPermutationGrandProductSlot{2} proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2} proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2} aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2} proofLookupSPolyOpeningAtZOmegaSlot{2} lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2} proofLookupGrandProductOpeningAtZOmegaSlot{2} lookupGrandProductFirstAggregatedCommitmentCoeff{2} queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
          aggregationChallenge{1} = W256.one /\ W256.to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2} /\
          exists p,
          aggregatedAtZSlot{2} = EllipticCurve.F_to_int_point p /\
          Primops.memory{1} = pointAddIntoDest_memory_footprint (store (store mem0 AGGREGATED_AT_Z_X_SLOT (W256.of_int queriesAtZ0Slot{2}.`1)) AGGREGATED_AT_Z_Y_SLOT (W256.of_int queriesAtZ0Slot{2}.`2)) AGGREGATED_AT_Z_X_SLOT aggregatedAtZSlot1 queriesAtZ1Slot1 p
        )
      ).
          wp.
          call (pointAddIntoDest_low_equiv_mid mem1 AGGREGATED_AT_Z_X_SLOT QUERIES_AT_Z_1_X_SLOT AGGREGATED_AT_Z_X_SLOT aggregatedAtZSlot1 queriesAtZ1Slot1). skip. progress.
          rewrite /AGGREGATED_AT_Z_X_SLOT Utils.uint256_cast_neg of_uintK. progress.
          rewrite /QUERIES_AT_Z_1_X_SLOT Utils.uint256_cast_neg of_uintK. progress.
          smt (). smt (). smt (). smt (). smt (). smt (). smt (). smt ().
          rewrite load_store_diff.
          rewrite /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. progress.
          rewrite /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. progress.
          rewrite load_store_same of_uintK modz_small. progress. smt ().
          apply (Utils.lt_trans _ FieldQ.p). smt (). rewrite -Constants.q_eq_fieldq_p. smt ().
          reflexivity.

          rewrite /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. progress. rewrite load_store_same of_uintK modz_small. progress. smt ().
          apply (Utils.lt_trans _ FieldQ.p). smt (). rewrite -Constants.q_eq_fieldq_p. smt ().
          reflexivity.

          rewrite /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /QUERIES_AT_Z_1_X_SLOT. progress.
          rewrite load_store_diff. progress. progress.
          rewrite load_store_diff. progress. progress.
          smt ().

          rewrite /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /QUERIES_AT_Z_1_X_SLOT. progress.
          rewrite load_store_diff. progress. progress.
          rewrite load_store_diff. progress. progress.
          smt ().
      
          case reverted_L.
          progress. right. smt ().
          progress.  smt (@Utils).
        have L :
      (
        exists (x y : FieldQ.F),
        ecAdd_precompile ((FieldQ.inF queriesAtZ0Slot{2}.`1))
          ((FieldQ.inF queriesAtZ0Slot{2}.`2))
          ((FieldQ.inF queriesAtZ1Slot{2}.`1))
          ((FieldQ.inF queriesAtZ1Slot{2}.`2)) =
        Some (x, y) /\
        result_R = Some ((FieldQ.asint x), (FieldQ.asint y)) /\
        memory_L =
        pointAddIntoDest_memory_footprint
          ((PurePrimops.mstore
              ((PurePrimops.mstore mem0 AGGREGATED_AT_Z_X_SLOT
                  ((of_int queriesAtZ0Slot{2}.`1))%W256))%PurePrimops
              AGGREGATED_AT_Z_Y_SLOT ((of_int queriesAtZ0Slot{2}.`2))%W256))%PurePrimops
          AGGREGATED_AT_Z_X_SLOT queriesAtZ0Slot{2} queriesAtZ1Slot{2} (
          x, y)
        ). smt ().
            case L. progress. exists (x, y). progress.
        
            seq 2 1 :
        (
          Primops.reverted{1} /\ failed{2} \/
          !Primops.reverted{1} /\
          !failed{2} /\
          prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2}
          proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2}
          proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2}
          proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2}
          proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2}
          proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2}
          vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2}
          vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2}
          vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2}
          vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2}
          proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2}
          proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2}
          proofLookupTableTypePolyOpeningAtZSlot{2}
          copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2}
          proofCopyPermutationGrandProductSlot{2}
          proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2}
          proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2}
          aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2}
          proofLookupSPolyOpeningAtZOmegaSlot{2}
          lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2}
          proofLookupGrandProductOpeningAtZOmegaSlot{2}
          lookupGrandProductFirstAggregatedCommitmentCoeff{2}
          queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
          W256.to_uint aggregationChallenge{1} = aggregationChallenge{2} /\
          0 <= aggregationChallenge{2} < FieldR.p /\
          W256.to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2} /\
          exists (p : FieldQ.F * FieldQ.F),
          aggregatedAtZSlot{2} = F_to_int_point p /\
          Primops.memory{1} =
          pointAddIntoDest_memory_footprint
          ((PurePrimops.mstore
              ((PurePrimops.mstore mem0 AGGREGATED_AT_Z_X_SLOT
                  ((of_int queriesAtZ0Slot{2}.`1))%W256))
                    AGGREGATED_AT_Z_Y_SLOT ((of_int queriesAtZ0Slot{2}.`2))%W256))
                    AGGREGATED_AT_Z_X_SLOT aggregatedAtZSlot1 queriesAtZ1Slot1 p
    ).
            inline *. wp. skip. progress.
            case H.
        move=>H. left. smt ().
        progress. right. rewrite /mulmod -Constants.R_int. progress.

        have ->:
        PurePrimops.mload
    (pointAddIntoDest_memory_footprint
      ((PurePrimops.mstore
          ((PurePrimops.mstore mem0 AGGREGATED_AT_Z_X_SLOT
              ((of_int queriesAtZ0Slot{2}.`1))%W256))%PurePrimops
                AGGREGATED_AT_Z_Y_SLOT ((of_int queriesAtZ0Slot{2}.`2))%W256))%PurePrimops
      AGGREGATED_AT_Z_X_SLOT aggregatedAtZSlot1 queriesAtZ1Slot1 p)
    STATE_V_SLOT = PurePrimops.mload mem0 STATE_V_SLOT.
                rewrite /pointAddIntoDest_memory_footprint. simplify.
                rewrite /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
                do 8! (rewrite load_store_diff; progress).
    
                rewrite of_uintK Utils.mod_mod_eq_mod. smt (). smt (). smt ().

                smt ().
                rewrite -Constants.r_eq_fieldr_p. smt ().
                exists p. progress.
    
                 seq 3 1 :
       (
         Primops.reverted{1} /\ failed{2} \/
         !Primops.reverted{1} /\
         !failed{2} /\
         prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2}
         proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2}
         proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2}
         proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2}
         proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2}
         proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2}
         vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2}
         vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2}
         vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2}
         vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2}
         proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2}
         proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2}
         proofLookupTableTypePolyOpeningAtZSlot{2}
         copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2}
         proofCopyPermutationGrandProductSlot{2}
         proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2}
         proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2}
         aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2}
         proofLookupSPolyOpeningAtZOmegaSlot{2}
         lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2}
         proofLookupGrandProductOpeningAtZOmegaSlot{2}
         lookupGrandProductFirstAggregatedCommitmentCoeff{2}
         queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
         W256.to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2} /\
         aggregationChallenge{1} = W256.of_int aggregationChallenge{2} /\
         0 <= aggregationChallenge{2} < FieldR.p /\
         exists (p : FieldQ.F * FieldQ.F),
         aggregatedAtZSlot{2} = F_to_int_point p /\
         Primops.memory{1} =
         pointAddIntoDest_memory_footprint mem0 AGGREGATED_AT_Z_X_SLOT aggregatedAtZSlot1 queriesAtZ1Slot1 p
       ).
           inline *. wp. skip. progress.
           case H.
           progress. left. by progress.
           progress. right. progress.

           rewrite /addmod /mulmod -Constants.R_int.
           simplify.

           rewrite /pointAddIntoDest_memory_footprint /PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. simplify.
           do 8! ((rewrite load_store_diff; first by progress); first by progress).
           have ->: W256.to_uint (PurePrimops.mload mem0 (W256.of_int 3104)) = proofLinearisationPolyOpeningAtZSlot{2}. smt ().
           rewrite of_uintK of_uintK.
           rewrite Utils.mod_mod_eq_mod. smt (). smt ().
           rewrite Utils.mod_mod_eq_mod. smt (). smt ().
           rewrite Constants.r_eq_fieldr_p. smt (@IntDiv).
       
           exists p. progress.

         rewrite /pointAddIntoDest_memory_footprint. progress.
         rewrite /AGGREGATED_AT_Z_Y_SLOT /AGGREGATED_AT_Z_X_SLOT. simplify.
         do 5! (rewrite (store_store_swap_diff _ (W256.of_int 4512)); progress).
         rewrite store_store_same.
         do 6! (rewrite (store_store_swap_diff _ (W256.of_int 4480)); progress).
         rewrite store_store_same.
         rewrite (store_store_swap_diff _ (W256.of_int 4480)); progress.
       
           seq 1 3 :
       (
         (Primops.reverted{1} /\ failed{2}) \/
         (
           !Primops.reverted{1} /\
           !failed{2} /\
           prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2}
           proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2}
           proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2}
           proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2}
           proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2}
           proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2}
           vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2}
           vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2}
           vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2}
           vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2}
           proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2}
           proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2}
           proofLookupTableTypePolyOpeningAtZSlot{2}
           copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2}
           proofCopyPermutationGrandProductSlot{2}
           proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2}
           proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2}
           aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2}
           proofLookupSPolyOpeningAtZOmegaSlot{2}
           lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2}
           proofLookupGrandProductOpeningAtZOmegaSlot{2}
           lookupGrandProductFirstAggregatedCommitmentCoeff{2}
           queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
           to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2} /\
           W256.to_uint aggregationChallenge{1} = aggregationChallenge{2} /\
           exists (x y : int) (newAggregateAtZSlot : FieldQ.F * FieldQ.F) (p : int * int),
           Primops.memory{1} = UpdateAggregationChallenge_footprint x y (FieldQ.asint newAggregateAtZSlot.`1) (FieldQ.asint newAggregateAtZSlot.`2) p mem0 /\
           aggregatedAtZSlot{2} = (FieldQ.asint newAggregateAtZSlot.`1, FieldQ.asint newAggregateAtZSlot.`2)
         )
       ).
           wp.
           exists* proofStatePolys0XSlot{2}.
           elim*=> proofStatePolys0XSlot_val.
           progress.
           exists* proofStatePolys0OpeningAtZSlot{2}.
           elim*=> proofStatePolys0OpeningAtZSlot_val.
           exists* aggregationChallenge{1}.
           elim*=> aggregationChallenge_val.
           exists* aggregatedOpeningAtZ{1}.
           elim*=> aggregatedOpeningAtZ_val.
           exists* v_challenge{2}.
           elim*=> v_challenge.
           exists* Primops.memory{1}.
           elim*=> mem2.
           exists* failed{2}.
           elim*=> failed2.
           case failed2.
           call UpdateAggregationChallenge_mid_of_low_er. skip. progress. smt (). left. smt ().
           call (UpdateAggregationChallenge_mid_of_low proofStatePolys0XSlot_val (F_to_int_point p) proofStatePolys0OpeningAtZSlot_val aggregationChallenge_val aggregatedOpeningAtZ_val v_challenge PROOF_STATE_POLYS_0_X_SLOT PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT mem2). skip. rewrite Constants.q_eq_fieldq_p.
           rewrite /prepareAggregatedCommitment_mem_inv /pointInField /isOpening; progress; case H; progress.
           exact F_to_int_point_1_ge_zero.
           exact F_to_int_point_1_lt_p.
           exact F_to_int_point_2_ge_zero.
           exact F_to_int_point_2_lt_p.
       
           by rewrite /PROOF_STATE_POLYS_0_X_SLOT W256.of_intN'; progress.
           by rewrite /PROOF_STATE_POLYS_0_X_SLOT; progress; rewrite W256.of_intN'; progress.
           by rewrite /PROOF_STATE_POLYS_0_X_SLOT W256.of_intN'; progress.
           rewrite /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT. progress.
           rewrite /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT. progress.
           rewrite /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT. progress.
           rewrite /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT. progress.

           rewrite of_uintK modz_small. progress. apply (Utils.lt_trans _ FieldR.p). assumption. rewrite -Constants.r_eq_fieldr_p. smt (). reflexivity.
       
           rewrite /pointAddIntoDest_memory_footprint /AGGREGATED_AT_Z_X_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress).

           rewrite /pointAddIntoDest_memory_footprint /AGGREGATED_AT_Z_X_SLOT /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress).

           rewrite /pointAddIntoDest_memory_footprint /AGGREGATED_AT_Z_X_SLOT /PROOF_STATE_POLYS_0_X_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress).

           rewrite H74 /PROOF_STATE_POLYS_0_X_SLOT. progress.

           rewrite /pointAddIntoDest_memory_footprint /AGGREGATED_AT_Z_X_SLOT /PROOF_STATE_POLYS_0_X_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress).

           rewrite H75 /PROOF_STATE_POLYS_0_Y_SLOT. progress.

           rewrite /pointAddIntoDest_memory_footprint /AGGREGATED_AT_Z_X_SLOT. simplify.
           rewrite load_store_diff; progress.
           rewrite load_store_same /F_to_int_point of_uintK modz_small. progress. smt (@Field).
           apply (Utils.lt_trans _ FieldQ.p). smt (@Field).
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           progress.

           rewrite /pointAddIntoDest_memory_footprint /AGGREGATED_AT_Z_X_SLOT. simplify.
           rewrite load_store_same /F_to_int_point. progress.
           rewrite of_uintK modz_small. progress. smt (@Field).
           apply (Utils.lt_trans _ FieldQ.p). smt (@Field).
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           reflexivity.

           progress. case H24. progress. progress. right. progress.

           exists x y newAggregateAtZSlot (F_to_int_point p).
           rewrite /UpdateAggregationChallenge_footprint /pointAddIntoDest_memory_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. progress.
           do 5! (rewrite (store_store_swap_diff _ _ W256.zero); progress). rewrite store_store_same.
           do 4! (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); progress). rewrite store_store_same.
           do 3! (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); progress). rewrite store_store_same.
           do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); progress). rewrite store_store_same.
           rewrite (store_store_swap_diff _ _ (W256.of_int 4512)); progress. rewrite store_store_same.
           rewrite (store_store_swap_diff _ _ (W256.of_int 4512)); progress. rewrite store_store_same.
           rewrite -(store_store_swap_diff _ _ (W256.of_int 4512)); progress.

           seq 1 3 :
       (
         (Primops.reverted{1} /\ failed{2}) \/
         (
           !Primops.reverted{1} /\
           !failed{2} /\
           prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2}
           proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2}
           proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2}
           proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2}
           proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2}
           proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2}
           vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2}
           vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2}
           vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2}
           vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2}
           proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2}
           proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2}
           proofLookupTableTypePolyOpeningAtZSlot{2}
           copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2}
           proofCopyPermutationGrandProductSlot{2}
           proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2}
           proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2}
           aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2}
           proofLookupSPolyOpeningAtZOmegaSlot{2}
           lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2}
           proofLookupGrandProductOpeningAtZOmegaSlot{2}
           lookupGrandProductFirstAggregatedCommitmentCoeff{2}
           queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
           to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2} /\
           W256.to_uint aggregationChallenge{1} = aggregationChallenge{2} /\
           exists (x y : int) (newAggregateAtZSlot : FieldQ.F * FieldQ.F) (p : int * int),
           Primops.memory{1} = UpdateAggregationChallenge_footprint x y (FieldQ.asint newAggregateAtZSlot.`1) (FieldQ.asint newAggregateAtZSlot.`2) p mem0 /\
           aggregatedAtZSlot{2} = (FieldQ.asint newAggregateAtZSlot.`1, FieldQ.asint newAggregateAtZSlot.`2)
         )
       ).
           wp.
           exists* proofStatePolys1Slot{2}.
           elim*=> proofStatePolys1Slot_val.
           progress.
           exists* proofStatePolys1OpeningAtZSlot{2}.
           elim*=> proofStatePolys1OpeningAtZSlot_val.
           exists* aggregationChallenge{1}.
           elim*=> aggregationChallenge_val.
           exists* aggregatedOpeningAtZ{1}.
           elim*=> aggregatedOpeningAtZ_val.
           exists* aggregatedAtZSlot{2}.
           elim*=> aggregatedAtZSlot.
           exists* v_challenge{2}.
           elim*=> v_challenge.
           exists* Primops.memory{1}.
           elim*=> mem2.
           exists* failed{2}.
           elim*=> failed2.
           case failed2.
           call UpdateAggregationChallenge_mid_of_low_er. skip. progress. smt (). left. smt ().
           call (UpdateAggregationChallenge_mid_of_low proofStatePolys1Slot_val aggregatedAtZSlot proofStatePolys1OpeningAtZSlot_val aggregationChallenge_val aggregatedOpeningAtZ_val v_challenge PROOF_STATE_POLYS_1_X_SLOT PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT mem2). skip. rewrite /PROOF_STATE_POLYS_1_X_SLOT /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT Constants.q_eq_fieldq_p.
           rewrite /prepareAggregatedCommitment_mem_inv /pointInField /isOpening. progress.

           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.



           exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.

           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           smt ().
           smt ().
           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_diff; progress.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().
           smt ().

           case reverted_L.
           progress. smt ().
           case H.
           progress.
           progress.
           smt ().
           smt ().
           smt ().

           have J :
       (
         exists (newAggregationChallenge newAggregatedOpeningAtZ : uint256)
         (newAggregateAtZSlot0 : FieldQ.F * FieldQ.F),
         result_R =
           Some
         (to_uint newAggregationChallenge, to_uint newAggregatedOpeningAtZ,
           F_to_int_point newAggregateAtZSlot0) /\
         (exists (x0 y0 : int),
           memory_L =
           UpdateAggregationChallenge_footprint x0 y0
           ((FieldQ.asint newAggregateAtZSlot0.`1))
           ((FieldQ.asint newAggregateAtZSlot0.`2))
           ((FieldQ.asint newAggregateAtZSlot.`1),
             (FieldQ.asint newAggregateAtZSlot.`2))
           (UpdateAggregationChallenge_footprint x y
             ((FieldQ.asint newAggregateAtZSlot.`1))
             ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0))
       ). smt ().
           case J. move => i i' newAggregateAtZSlot0 [req J].
           case J. move => x0 y0 J. exists x0 y0 newAggregateAtZSlot0 (F_to_int_point newAggregateAtZSlot). rewrite J. progress.

           rewrite /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. simplify.
           do 5! (rewrite (store_store_swap_diff _ _ W256.zero); progress).
           rewrite store_store_same.
           do 4! (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); progress).
           rewrite store_store_same.
           do 3! (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); progress).
           rewrite store_store_same.
           do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); progress).
           rewrite store_store_same.
           rewrite (store_store_swap_diff _ _ (W256.of_int 4480)); progress.
           rewrite store_store_same.
           rewrite store_store_same.
           reflexivity.
           rewrite req.
           smt ().

           seq 1 3 :
       (
         (Primops.reverted{1} /\ failed{2}) \/
         (
           !Primops.reverted{1} /\
           !failed{2} /\
           prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2}
           proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2}
           proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2}
           proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2}
           proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2}
           proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2}
           vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2}
           vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2}
           vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2}
           vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2}
           proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2}
           proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2}
           proofLookupTableTypePolyOpeningAtZSlot{2}
           copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2}
           proofCopyPermutationGrandProductSlot{2}
           proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2}
           proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2}
           aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2}
           proofLookupSPolyOpeningAtZOmegaSlot{2}
           lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2}
           proofLookupGrandProductOpeningAtZOmegaSlot{2}
           lookupGrandProductFirstAggregatedCommitmentCoeff{2}
           queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
           to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2} /\
           W256.to_uint aggregationChallenge{1} = aggregationChallenge{2} /\
           exists (x y : int) (newAggregateAtZSlot : FieldQ.F * FieldQ.F) (p : int * int),
           Primops.memory{1} = UpdateAggregationChallenge_footprint x y (FieldQ.asint newAggregateAtZSlot.`1) (FieldQ.asint newAggregateAtZSlot.`2) p mem0 /\
           aggregatedAtZSlot{2} = (FieldQ.asint newAggregateAtZSlot.`1, FieldQ.asint newAggregateAtZSlot.`2)
         )
       ).
           wp.
           exists* proofStatePolys2Slot{2}.
           elim*=> proofStatePolys2Slot_val.
           progress.
           exists* proofStatePolys2OpeningAtZSlot{2}.
           elim*=> proofStatePolys2OpeningAtZSlot_val.
           exists* aggregationChallenge{1}.
           elim*=> aggregationChallenge_val.
           exists* aggregatedOpeningAtZ{1}.
           elim*=> aggregatedOpeningAtZ_val.
           exists* aggregatedAtZSlot{2}.
           elim*=> aggregatedAtZSlot.
           exists* v_challenge{2}.
           elim*=> v_challenge.
           exists* Primops.memory{1}.
           elim*=> mem2.
           exists* failed{2}.
           elim*=> failed2.
           case failed2.
           call UpdateAggregationChallenge_mid_of_low_er. skip. progress. smt (). left. smt ().
           call (UpdateAggregationChallenge_mid_of_low proofStatePolys2Slot_val aggregatedAtZSlot proofStatePolys2OpeningAtZSlot_val aggregationChallenge_val aggregatedOpeningAtZ_val v_challenge PROOF_STATE_POLYS_2_X_SLOT PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT mem2). skip. rewrite /PROOF_STATE_POLYS_2_X_SLOT /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT Constants.q_eq_fieldq_p.
           rewrite /prepareAggregatedCommitment_mem_inv /pointInField /isOpening. progress.

           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.



           exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.

           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           smt (@W256).
           smt ().
           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_diff; progress.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().
           smt ().

           case reverted_L.
           progress. smt ().
           case H.
           progress.
           progress.
           smt ().
           smt ().
           smt ().

           have J :
       (
         exists (newAggregationChallenge newAggregatedOpeningAtZ : uint256)
         (newAggregateAtZSlot0 : FieldQ.F * FieldQ.F),
         result_R =
           Some
         (to_uint newAggregationChallenge, to_uint newAggregatedOpeningAtZ,
           F_to_int_point newAggregateAtZSlot0) /\
         (exists (x0 y0 : int),
           memory_L =
           UpdateAggregationChallenge_footprint x0 y0
           ((FieldQ.asint newAggregateAtZSlot0.`1))
           ((FieldQ.asint newAggregateAtZSlot0.`2))
           ((FieldQ.asint newAggregateAtZSlot.`1),
             (FieldQ.asint newAggregateAtZSlot.`2))
           (UpdateAggregationChallenge_footprint x y
             ((FieldQ.asint newAggregateAtZSlot.`1))
             ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0))
       ). smt ().
           case J. move => i i' newAggregateAtZSlot0 [req J].
           case J. move => x0 y0 J. exists x0 y0 newAggregateAtZSlot0 (F_to_int_point newAggregateAtZSlot). rewrite J. progress.

           rewrite /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. simplify.
           do 5! (rewrite (store_store_swap_diff _ _ W256.zero); progress).
           rewrite store_store_same.
           do 4! (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); progress).
           rewrite store_store_same.
           do 3! (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); progress).
           rewrite store_store_same.
           do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); progress).
           rewrite store_store_same.
           rewrite (store_store_swap_diff _ _ (W256.of_int 4480)); progress.
           rewrite store_store_same.
           rewrite store_store_same.
           reflexivity.
           rewrite req.
           smt ().

       
           seq 3 2 : (
           Primops.reverted{1} /\ failed{2} \/
           !Primops.reverted{1} /\
           !failed{2} /\
           prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2}
           proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2}
           proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2}
           proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2}
           proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2}
           proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2}
           vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2}
           vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2}
           vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2}
           vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2}
           proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2}
           proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2}
           proofLookupTableTypePolyOpeningAtZSlot{2}
           copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2}
           proofCopyPermutationGrandProductSlot{2}
           proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2}
           proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2}
           aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2}
           proofLookupSPolyOpeningAtZOmegaSlot{2}
           lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2}
           proofLookupGrandProductOpeningAtZOmegaSlot{2}
           lookupGrandProductFirstAggregatedCommitmentCoeff{2}
           queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
         to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2} /\
         to_uint aggregationChallenge{1} = aggregationChallenge{2} /\
         W256.to_uint firstDCoeff{1} = firstDCoeff{2} /\
           exists (x y : int) (newAggregateAtZSlot : FieldQ.F * FieldQ.F) (p : int *
           int),
           Primops.memory{1} =
           UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0 /\
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ).
           inline mload. sp. skip. progress.
           case H.
           progress. left. progress.
           progress. right. progress.

           rewrite /UpdateAggregationChallenge_footprint /STATE_V_SLOT /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /mulmod. simplify.
           do 6! (rewrite load_store_diff; progress).
           rewrite -Constants.R_int of_uintK Utils.mod_mod_eq_mod /Constants.R; progress. congr. congr. congr. smt ().

           rewrite /UpdateAggregationChallenge_footprint /STATE_V_SLOT /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /mulmod. simplify.
           do 6! (rewrite load_store_diff; progress).
           rewrite -Constants.R_int of_uintK Utils.mod_mod_eq_mod /Constants.R; progress. congr. congr. congr. smt ().
       
           exists x y newAggregateAtZSlot p. progress.
       
           seq 3 1 : #pre.

           inline mload. sp. skip. progress.
           case H.
           progress. left. progress.
           progress. right. progress.

           rewrite /UpdateAggregationChallenge_footprint /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /mulmod /addmod. simplify.
           do 6! (rewrite load_store_diff; progress).
           rewrite -Constants.R_int of_uintK of_uintK Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. rewrite /Constants.R. progress.
           rewrite Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. rewrite /Constants.R. progress.
           smt (@IntDiv).

           exists x y newAggregateAtZSlot p. progress.

           seq 1 3 : #pre.
           wp.
           exists* vkGateSelectors0Slot{2}.
           elim*=> vkGateSelectors0Slot_val.
           progress.
           exists* proofGateSelectors0OpeningAtZSlot{2}.
           elim*=> proofGateSelectors0OpeningAtZSlot_val.
           exists* aggregationChallenge{1}.
           elim*=> aggregationChallenge_val.
           exists* aggregatedOpeningAtZ{1}.
           elim*=> aggregatedOpeningAtZ_val.
           exists* aggregatedAtZSlot{2}.
           elim*=> aggregatedAtZSlot.
           exists* v_challenge{2}.
           elim*=> v_challenge.
           exists* Primops.memory{1}.
           elim*=> mem2.
           exists* failed{2}.
           elim*=> failed2.
           case failed2.
           call UpdateAggregationChallenge_mid_of_low_er. skip. progress. smt (). left. smt ().
           call (UpdateAggregationChallenge_mid_of_low vkGateSelectors0Slot_val aggregatedAtZSlot proofGateSelectors0OpeningAtZSlot_val aggregationChallenge_val aggregatedOpeningAtZ_val v_challenge VK_GATE_SELECTORS_0_X_SLOT PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT mem2). skip. rewrite /VK_GATE_SELECTORS_0_X_SLOT /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT Constants.q_eq_fieldq_p.
           rewrite /prepareAggregatedCommitment_mem_inv /pointInField /isOpening. progress.

           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.

           exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.

           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           smt (@W256).
           smt ().
           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_diff; progress.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().
           smt ().

           case reverted_L.
           progress. smt ().
           case H.
           progress.
           progress.
           smt ().
           smt ().
           smt ().

           have J :
       (
         exists (newAggregationChallenge newAggregatedOpeningAtZ : uint256)
         (newAggregateAtZSlot0 : FieldQ.F * FieldQ.F),
         result_R =
           Some
         (to_uint newAggregationChallenge, to_uint newAggregatedOpeningAtZ,
           F_to_int_point newAggregateAtZSlot0) /\
         (exists (x0 y0 : int),
           memory_L =
           UpdateAggregationChallenge_footprint x0 y0
           ((FieldQ.asint newAggregateAtZSlot0.`1))
           ((FieldQ.asint newAggregateAtZSlot0.`2))
           ((FieldQ.asint newAggregateAtZSlot.`1),
             (FieldQ.asint newAggregateAtZSlot.`2))
           (UpdateAggregationChallenge_footprint x y
             ((FieldQ.asint newAggregateAtZSlot.`1))
             ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0))
       ). smt ().
           case J. move => i i' newAggregateAtZSlot0 [req J].
           case J. move => x0 y0 J. exists x0 y0 newAggregateAtZSlot0 (F_to_int_point newAggregateAtZSlot). rewrite J. progress.

           rewrite /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. simplify.
           do 5! (rewrite (store_store_swap_diff _ _ W256.zero); progress).
           rewrite store_store_same.
           do 4! (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); progress).
           rewrite store_store_same.
           do 3! (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); progress).
           rewrite store_store_same.
           do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); progress).
           rewrite store_store_same.
           rewrite (store_store_swap_diff _ _ (W256.of_int 4480)); progress.
           rewrite store_store_same.
           rewrite store_store_same.
           reflexivity.
           rewrite req.
           smt ().

       seq 1 3 : #pre.
           wp.
           exists* vkPermutation0Slot{2}.
           elim*=> vkPermutation0Slot_val.
           progress.
           exists* proofCopyPermutationPolys0OpeningAtZSlot{2}.
           elim*=> proofCopyPermutationPolys0OpeningAtZSlot_val.
           exists* aggregationChallenge{1}.
           elim*=> aggregationChallenge_val.
           exists* aggregatedOpeningAtZ{1}.
           elim*=> aggregatedOpeningAtZ_val.
           exists* aggregatedAtZSlot{2}.
           elim*=> aggregatedAtZSlot.
           exists* v_challenge{2}.
           elim*=> v_challenge.
           exists* Primops.memory{1}.
           elim*=> mem2.
           exists* failed{2}.
           elim*=> failed2.
           case failed2.
           call UpdateAggregationChallenge_mid_of_low_er. skip. progress. smt (). left. smt ().
           call (UpdateAggregationChallenge_mid_of_low vkPermutation0Slot_val aggregatedAtZSlot proofCopyPermutationPolys0OpeningAtZSlot_val aggregationChallenge_val aggregatedOpeningAtZ_val v_challenge VK_PERMUTATION_0_X_SLOT PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT mem2). skip. rewrite /VK_PERMUTATION_0_X_SLOT /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT Constants.q_eq_fieldq_p.
           rewrite /prepareAggregatedCommitment_mem_inv /pointInField /isOpening. progress.

           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.

           exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.

           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           smt (@W256).
           smt ().
           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_diff; progress.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().
           smt ().

           case reverted_L.
           progress. smt ().
           case H.
           progress.
           progress.
           smt ().
           smt ().
           smt ().

           have J :
       (
         exists (newAggregationChallenge newAggregatedOpeningAtZ : uint256)
         (newAggregateAtZSlot0 : FieldQ.F * FieldQ.F),
         result_R =
           Some
         (to_uint newAggregationChallenge, to_uint newAggregatedOpeningAtZ,
           F_to_int_point newAggregateAtZSlot0) /\
         (exists (x0 y0 : int),
           memory_L =
           UpdateAggregationChallenge_footprint x0 y0
           ((FieldQ.asint newAggregateAtZSlot0.`1))
           ((FieldQ.asint newAggregateAtZSlot0.`2))
           ((FieldQ.asint newAggregateAtZSlot.`1),
             (FieldQ.asint newAggregateAtZSlot.`2))
           (UpdateAggregationChallenge_footprint x y
             ((FieldQ.asint newAggregateAtZSlot.`1))
             ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0))
       ). smt ().
           case J. move => i i' newAggregateAtZSlot0 [req J].
           case J. move => x0 y0 J. exists x0 y0 newAggregateAtZSlot0 (F_to_int_point newAggregateAtZSlot). rewrite J. progress.

           rewrite /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. simplify.
           do 5! (rewrite (store_store_swap_diff _ _ W256.zero); progress).
           rewrite store_store_same.
           do 4! (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); progress).
           rewrite store_store_same.
           do 3! (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); progress).
           rewrite store_store_same.
           do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); progress).
           rewrite store_store_same.
           rewrite (store_store_swap_diff _ _ (W256.of_int 4480)); progress.
           rewrite store_store_same.
           rewrite store_store_same.
           reflexivity.
           rewrite req.
           smt ().

       seq 1 3 : #pre.
           wp.
           exists* vkPermutation1Slot{2}.
           elim*=> vkPermutation1Slot_val.
           progress.
           exists* proofCopyPermutationPolys1OpeningAtZSlot{2}.
           elim*=> proofCopyPermutationPolys1OpeningAtZSlot_val.
           exists* aggregationChallenge{1}.
           elim*=> aggregationChallenge_val.
           exists* aggregatedOpeningAtZ{1}.
           elim*=> aggregatedOpeningAtZ_val.
           exists* aggregatedAtZSlot{2}.
           elim*=> aggregatedAtZSlot.
           exists* v_challenge{2}.
           elim*=> v_challenge.
           exists* Primops.memory{1}.
           elim*=> mem2.
           exists* failed{2}.
           elim*=> failed2.
           case failed2.
           call UpdateAggregationChallenge_mid_of_low_er. skip. progress. smt (). left. smt ().
           call (UpdateAggregationChallenge_mid_of_low vkPermutation1Slot_val aggregatedAtZSlot proofCopyPermutationPolys1OpeningAtZSlot_val aggregationChallenge_val aggregatedOpeningAtZ_val v_challenge VK_PERMUTATION_1_X_SLOT PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT mem2). skip. rewrite /VK_PERMUTATION_1_X_SLOT /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT Constants.q_eq_fieldq_p.
           rewrite /prepareAggregatedCommitment_mem_inv /pointInField /isOpening. progress.

           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.

           exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.

           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           smt (@W256).
           smt ().
           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_diff; progress.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().
           smt ().

           case reverted_L.
           progress. smt ().
           case H.
           progress.
           progress.
           smt ().
           smt ().
           smt ().

           have J :
       (
         exists (newAggregationChallenge newAggregatedOpeningAtZ : uint256)
         (newAggregateAtZSlot0 : FieldQ.F * FieldQ.F),
         result_R =
           Some
         (to_uint newAggregationChallenge, to_uint newAggregatedOpeningAtZ,
           F_to_int_point newAggregateAtZSlot0) /\
         (exists (x0 y0 : int),
           memory_L =
           UpdateAggregationChallenge_footprint x0 y0
           ((FieldQ.asint newAggregateAtZSlot0.`1))
           ((FieldQ.asint newAggregateAtZSlot0.`2))
           ((FieldQ.asint newAggregateAtZSlot.`1),
             (FieldQ.asint newAggregateAtZSlot.`2))
           (UpdateAggregationChallenge_footprint x y
             ((FieldQ.asint newAggregateAtZSlot.`1))
             ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0))
       ). smt ().
           case J. move => i i' newAggregateAtZSlot0 [req J].
           case J. move => x0 y0 J. exists x0 y0 newAggregateAtZSlot0 (F_to_int_point newAggregateAtZSlot). rewrite J. progress.

           rewrite /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. simplify.
           do 5! (rewrite (store_store_swap_diff _ _ W256.zero); progress).
           rewrite store_store_same.
           do 4! (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); progress).
           rewrite store_store_same.
           do 3! (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); progress).
           rewrite store_store_same.
           do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); progress).
           rewrite store_store_same.
           rewrite (store_store_swap_diff _ _ (W256.of_int 4480)); progress.
           rewrite store_store_same.
           rewrite store_store_same.
           reflexivity.
           rewrite req.
           smt ().

       seq 1 3 : #pre.
           wp.
           exists* vkPermutation2Slot{2}.
           elim*=> vkPermutation2Slot_val.
           progress.
           exists* proofCopyPermutationPolys2OpeningAtZSlot{2}.
           elim*=> proofCopyPermutationPolys2OpeningAtZSlot_val.
           exists* aggregationChallenge{1}.
           elim*=> aggregationChallenge_val.
           exists* aggregatedOpeningAtZ{1}.
           elim*=> aggregatedOpeningAtZ_val.
           exists* aggregatedAtZSlot{2}.
           elim*=> aggregatedAtZSlot.
           exists* v_challenge{2}.
           elim*=> v_challenge.
           exists* Primops.memory{1}.
           elim*=> mem2.
           exists* failed{2}.
           elim*=> failed2.
           case failed2.
           call UpdateAggregationChallenge_mid_of_low_er. skip. progress. smt (). left. smt ().
           call (UpdateAggregationChallenge_mid_of_low vkPermutation2Slot_val aggregatedAtZSlot proofCopyPermutationPolys2OpeningAtZSlot_val aggregationChallenge_val aggregatedOpeningAtZ_val v_challenge VK_PERMUTATION_2_X_SLOT PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT mem2). skip. rewrite /VK_PERMUTATION_2_X_SLOT /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT Constants.q_eq_fieldq_p.
           rewrite /prepareAggregatedCommitment_mem_inv /pointInField /isOpening. progress.

           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.

           exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.

           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           smt (@W256).
           smt ().
           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_diff; progress.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().
           smt ().

           case reverted_L.
           progress. smt ().
           case H.
           progress.
           progress.
           smt ().
           smt ().
           smt ().

           have J :
       (
         exists (newAggregationChallenge newAggregatedOpeningAtZ : uint256)
         (newAggregateAtZSlot0 : FieldQ.F * FieldQ.F),
         result_R =
           Some
         (to_uint newAggregationChallenge, to_uint newAggregatedOpeningAtZ,
           F_to_int_point newAggregateAtZSlot0) /\
         (exists (x0 y0 : int),
           memory_L =
           UpdateAggregationChallenge_footprint x0 y0
           ((FieldQ.asint newAggregateAtZSlot0.`1))
           ((FieldQ.asint newAggregateAtZSlot0.`2))
           ((FieldQ.asint newAggregateAtZSlot.`1),
             (FieldQ.asint newAggregateAtZSlot.`2))
           (UpdateAggregationChallenge_footprint x y
             ((FieldQ.asint newAggregateAtZSlot.`1))
             ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0))
       ). smt ().
           case J. move => i i' newAggregateAtZSlot0 [req J].
           case J. move => x0 y0 J. exists x0 y0 newAggregateAtZSlot0 (F_to_int_point newAggregateAtZSlot). rewrite J. progress.

           rewrite /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. simplify.
           do 5! (rewrite (store_store_swap_diff _ _ W256.zero); progress).
           rewrite store_store_same.
           do 4! (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); progress).
           rewrite store_store_same.
           do 3! (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); progress).
           rewrite store_store_same.
           do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); progress).
           rewrite store_store_same.
           rewrite (store_store_swap_diff _ _ (W256.of_int 4480)); progress.
           rewrite store_store_same.
           rewrite store_store_same.
           reflexivity.
           rewrite req.
           smt ().

       seq 3 2 : (
           Primops.reverted{1} /\ failed{2} \/
           !Primops.reverted{1} /\
           !failed{2} /\
           prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2}
           proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2}
           proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2}
           proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2}
           proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2}
           proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2}
           vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2}
           vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2}
           vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2}
           vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2}
           proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2}
           proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2}
           proofLookupTableTypePolyOpeningAtZSlot{2}
           copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2}
           proofCopyPermutationGrandProductSlot{2}
           proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2}
           proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2}
           aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2}
           proofLookupSPolyOpeningAtZOmegaSlot{2}
           lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2}
           proofLookupGrandProductOpeningAtZOmegaSlot{2}
           lookupGrandProductFirstAggregatedCommitmentCoeff{2}
           queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
         to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2} /\
         to_uint aggregationChallenge{1} = aggregationChallenge{2} /\
           W256.to_uint firstDCoeff{1} = firstDCoeff{2} /\
           W256.to_uint firstTCoeff{1} = firstTCoeff{2} /\
           exists (x y : int) (newAggregateAtZSlot : FieldQ.F * FieldQ.F) (p : int *
           int),
           Primops.memory{1} =
           UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0 /\
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ).
           inline mload. sp. skip. progress.
           case H.
           progress. left. progress.
           progress. right. progress.

           rewrite /UpdateAggregationChallenge_footprint /STATE_V_SLOT /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /mulmod. simplify.
           do 6! (rewrite load_store_diff; progress).
           rewrite -Constants.R_int of_uintK Utils.mod_mod_eq_mod /Constants.R; progress. congr. congr. smt ().

           rewrite /UpdateAggregationChallenge_footprint /STATE_V_SLOT /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /mulmod. simplify.
           do 6! (rewrite load_store_diff; progress).
           rewrite -Constants.R_int of_uintK Utils.mod_mod_eq_mod /Constants.R; progress. congr. congr. smt ().
       
           exists x y newAggregateAtZSlot p. progress.

           seq 3 1 : #pre.

           inline mload. sp. skip. progress.
           case H.
           progress. left. progress.
           progress. right. progress.

           rewrite /UpdateAggregationChallenge_footprint /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /mulmod /addmod. simplify.
           do 6! (rewrite load_store_diff; progress).
           rewrite -Constants.R_int of_uintK of_uintK Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. rewrite /Constants.R. progress.
           rewrite Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. rewrite /Constants.R. progress.
           have ->: to_uint ((PurePrimops.mload mem0 ((of_int 2944))%W256)) = proofLookupTPolyOpeningAtZSlot{2}. smt ().
       
           smt (@IntDiv).

           exists x y newAggregateAtZSlot p. progress.

       seq 1 3 : #pre.
           wp.
           exists* vkLookupSelectorSlot{2}.
           elim*=> vkLookupSelectorSlot_val.
           progress.
           exists* proofLookupSelectorPolyOpeningAtZSlot{2}.
           elim*=> proofLookupSelectorPolyOpeningAtZSlot_val.
           exists* aggregationChallenge{1}.
           elim*=> aggregationChallenge_val.
           exists* aggregatedOpeningAtZ{1}.
           elim*=> aggregatedOpeningAtZ_val.
           exists* aggregatedAtZSlot{2}.
           elim*=> aggregatedAtZSlot.
           exists* v_challenge{2}.
           elim*=> v_challenge.
           exists* Primops.memory{1}.
           elim*=> mem2.
           exists* failed{2}.
           elim*=> failed2.
           case failed2.
           call UpdateAggregationChallenge_mid_of_low_er. skip. progress. smt (). left. smt ().
           call (UpdateAggregationChallenge_mid_of_low vkLookupSelectorSlot_val aggregatedAtZSlot proofLookupSelectorPolyOpeningAtZSlot_val aggregationChallenge_val aggregatedOpeningAtZ_val v_challenge VK_LOOKUP_SELECTOR_X_SLOT PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT mem2). skip. rewrite /VK_LOOKUP_SELECTOR_X_SLOT /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT Constants.q_eq_fieldq_p.
           rewrite /prepareAggregatedCommitment_mem_inv /pointInField /isOpening. progress.

           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.

           exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.

           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           smt (@W256).
           smt ().
           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_diff; progress.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().
           smt ().

           case reverted_L.
           progress. smt ().
           case H.
           progress.
           progress.
           smt ().
           smt ().
           smt ().

           have J :
       (
         exists (newAggregationChallenge newAggregatedOpeningAtZ : uint256)
         (newAggregateAtZSlot0 : FieldQ.F * FieldQ.F),
         result_R =
           Some
         (to_uint newAggregationChallenge, to_uint newAggregatedOpeningAtZ,
           F_to_int_point newAggregateAtZSlot0) /\
         (exists (x0 y0 : int),
           memory_L =
           UpdateAggregationChallenge_footprint x0 y0
           ((FieldQ.asint newAggregateAtZSlot0.`1))
           ((FieldQ.asint newAggregateAtZSlot0.`2))
           ((FieldQ.asint newAggregateAtZSlot.`1),
             (FieldQ.asint newAggregateAtZSlot.`2))
           (UpdateAggregationChallenge_footprint x y
             ((FieldQ.asint newAggregateAtZSlot.`1))
             ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0))
       ). smt ().
           case J. move => i i' newAggregateAtZSlot0 [req J].
           case J. move => x0 y0 J. exists x0 y0 newAggregateAtZSlot0 (F_to_int_point newAggregateAtZSlot). rewrite J. progress.

           rewrite /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. simplify.
           do 5! (rewrite (store_store_swap_diff _ _ W256.zero); progress).
           rewrite store_store_same.
           do 4! (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); progress).
           rewrite store_store_same.
           do 3! (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); progress).
           rewrite store_store_same.
           do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); progress).
           rewrite store_store_same.
           rewrite (store_store_swap_diff _ _ (W256.of_int 4480)); progress.
           rewrite store_store_same.
           rewrite store_store_same.
           reflexivity.
           rewrite req.
           smt ().

       seq 1 3 : #pre.
           wp.
           exists* vkLookupTableTypeSlot{2}.
           elim*=> vkLookupTableTypeSlot_val.
           progress.
           exists* proofLookupTableTypePolyOpeningAtZSlot{2}.
           elim*=> proofLookupTableTypePolyOpeningAtZSlot_val.
           exists* aggregationChallenge{1}.
           elim*=> aggregationChallenge_val.
           exists* aggregatedOpeningAtZ{1}.
           elim*=> aggregatedOpeningAtZ_val.
           exists* aggregatedAtZSlot{2}.
           elim*=> aggregatedAtZSlot.
           exists* v_challenge{2}.
           elim*=> v_challenge.
           exists* Primops.memory{1}.
           elim*=> mem2.
           exists* failed{2}.
           elim*=> failed2.
           case failed2.
           call UpdateAggregationChallenge_mid_of_low_er. skip. progress. smt (). left. smt ().
           call (UpdateAggregationChallenge_mid_of_low vkLookupTableTypeSlot_val aggregatedAtZSlot proofLookupTableTypePolyOpeningAtZSlot_val aggregationChallenge_val aggregatedOpeningAtZ_val v_challenge VK_LOOKUP_TABLE_TYPE_X_SLOT PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT mem2). skip. rewrite /VK_LOOKUP_TABLE_TYPE_X_SLOT /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT Constants.q_eq_fieldq_p.
           rewrite /prepareAggregatedCommitment_mem_inv /pointInField /isOpening. progress.

           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.
           case H; progress.

           exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.ge0_asint.
           have J :
       (
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ). smt ().
           rewrite J. simplify. exact FieldQ.gtp_asint.

           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           rewrite Utils.uint256_cast_neg. progress.
           smt (@W256).
           smt ().
           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           do 6! (rewrite load_store_diff; progress). smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_diff; progress.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().

           have J :
       (
         Primops.memory{1} =
         UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0
       ). smt ().
           rewrite J /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /STATE_V_SLOT. simplify.
           rewrite load_store_same of_uintK modz_small; progress.
           exact FieldQ.ge0_asint.
           apply (Utils.lt_trans _ FieldQ.p).
           exact FieldQ.gtp_asint.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. progress.
           smt ().
           smt ().

           case reverted_L.
           progress. smt ().
           case H.
           progress.
           progress.
           smt ().
           smt ().
           smt ().

           have J :
       (
         exists (newAggregationChallenge newAggregatedOpeningAtZ : uint256)
         (newAggregateAtZSlot0 : FieldQ.F * FieldQ.F),
         result_R =
           Some
         (to_uint newAggregationChallenge, to_uint newAggregatedOpeningAtZ,
           F_to_int_point newAggregateAtZSlot0) /\
         (exists (x0 y0 : int),
           memory_L =
           UpdateAggregationChallenge_footprint x0 y0
           ((FieldQ.asint newAggregateAtZSlot0.`1))
           ((FieldQ.asint newAggregateAtZSlot0.`2))
           ((FieldQ.asint newAggregateAtZSlot.`1),
             (FieldQ.asint newAggregateAtZSlot.`2))
           (UpdateAggregationChallenge_footprint x y
             ((FieldQ.asint newAggregateAtZSlot.`1))
             ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0))
       ). smt ().
           case J. move => i i' newAggregateAtZSlot0 [req J].
           case J. move => x0 y0 J. exists x0 y0 newAggregateAtZSlot0 (F_to_int_point newAggregateAtZSlot). rewrite J. progress.

           rewrite /UpdateAggregationChallenge_footprint /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT. simplify.
           do 5! (rewrite (store_store_swap_diff _ _ W256.zero); progress).
           rewrite store_store_same.
           do 4! (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); progress).
           rewrite store_store_same.
           do 3! (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); progress).
           rewrite store_store_same.
           do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); progress).
           rewrite store_store_same.
           rewrite (store_store_swap_diff _ _ (W256.of_int 4480)); progress.
           rewrite store_store_same.
           rewrite store_store_same.
           reflexivity.
           rewrite req.
           smt ().

           seq 1 1 :
       (
         Primops.reverted{1} /\ failed{2} \/
         !Primops.reverted{1} /\
         !failed{2} /\
         prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2}
         proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2}
         proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2}
         proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2}
         proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2}
         proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2}
         vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2}
         vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2}
         vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2}
         vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2}
         proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2}
         proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2}
         proofLookupTableTypePolyOpeningAtZSlot{2}
         copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2}
         proofCopyPermutationGrandProductSlot{2}
         proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2}
         proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2}
         aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2}
         proofLookupSPolyOpeningAtZOmegaSlot{2}
         lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2}
         proofLookupGrandProductOpeningAtZOmegaSlot{2}
         lookupGrandProductFirstAggregatedCommitmentCoeff{2}
         queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
         to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2} /\
         to_uint aggregationChallenge{1} = aggregationChallenge{2} /\
         to_uint firstDCoeff{1} = firstDCoeff{2} /\
         to_uint firstTCoeff{1} = firstTCoeff{2} /\
         exists (x y : int) (newAggregateAtZSlot : FieldQ.F * FieldQ.F) (p : int *
         int),
         Primops.memory{1} =
         PurePrimops.mstore
         (UpdateAggregationChallenge_footprint x y
         ((FieldQ.asint newAggregateAtZSlot.`1))
         ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0) AGGREGATED_OPENING_AT_Z_SLOT aggregatedOpeningAtZ{1} /\
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ).

           inline mstore. wp. skip. progress.
           case H.
           progress. left. progress.
           progress. right. progress.

           exists x y newAggregateAtZSlot p. progress.

           seq 2 1 : #pre.

           inline mload. wp. skip. progress.
           case H.
           progress. left. progress.
           progress. right. progress.

           rewrite /UpdateAggregationChallenge_footprint /STATE_V_SLOT /AGGREGATED_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /mulmod. simplify.

           do 7! (rewrite load_store_diff; progress).

           rewrite of_uintK -Constants.R_int Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. rewrite /Constants.R. progress.
           smt ().

           exists x y newAggregateAtZSlot p. progress.

           seq 4 1 :
       (
         Primops.reverted{1} /\ failed{2} \/
         !Primops.reverted{1} /\
         !failed{2} /\
         prepareAggregatedCommitment_mem_inv mem0 queriesAtZ0Slot{2}
         proofQuotientPolyOpeningAtZSlot{2} queriesAtZ1Slot{2} v_challenge{2}
         proofLinearisationPolyOpeningAtZSlot{2} proofStatePolys0XSlot{2}
         proofStatePolys0OpeningAtZSlot{2} proofStatePolys1Slot{2}
         proofStatePolys1OpeningAtZSlot{2} proofStatePolys2Slot{2}
         proofStatePolys2OpeningAtZSlot{2} proofStatePolys3OpeningAtZSlot{2}
         vkGateSelectors0Slot{2} proofGateSelectors0OpeningAtZSlot{2}
         vkPermutation0Slot{2} proofCopyPermutationPolys0OpeningAtZSlot{2}
         vkPermutation1Slot{2} proofCopyPermutationPolys1OpeningAtZSlot{2}
         vkPermutation2Slot{2} proofCopyPermutationPolys2OpeningAtZSlot{2}
         proofLookupTPolyOpeningAtZSlot{2} vkLookupSelectorSlot{2}
         proofLookupSelectorPolyOpeningAtZSlot{2} vkLookupTableTypeSlot{2}
         proofLookupTableTypePolyOpeningAtZSlot{2}
         copyPermutationFirstAggregatedCommitmentCoeff{2} u_challenge{2}
         proofCopyPermutationGrandProductSlot{2}
         proofCopyPermutationGrandProductOpeningAtZOmegaSlot{2}
         proofStatePolys3Slot{2} proofStatePolys3OpeningAtZOmegaSlot{2}
         aggregatedAtZOmegaSlot{2} proofLookupSPolySlot{2}
         proofLookupSPolyOpeningAtZOmegaSlot{2}
         lookupSFirstAggregatedCommitmentCoeff{2} proofLookupGrandProductSlot{2}
         proofLookupGrandProductOpeningAtZOmegaSlot{2}
         lookupGrandProductFirstAggregatedCommitmentCoeff{2}
         queriesTPolyAggregatedSlot{2} proofLookupTPolyOpeningAtZOmegaSlot{2} /\
         to_uint aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2} /\
         to_uint aggregationChallenge{1} = aggregationChallenge{2} /\
         to_uint firstDCoeff{1} = firstDCoeff{2} /\
         to_uint firstTCoeff{1} = firstTCoeff{2} /\
         to_uint copyPermutationCoeff{1} = copyPermutationCoeff{2} /\
         exists (x y : int) (newAggregateAtZSlot : FieldQ.F * FieldQ.F) (p : int *
         int),
         Primops.memory{1} =
         (PurePrimops.mstore
           (UpdateAggregationChallenge_footprint x y
             ((FieldQ.asint newAggregateAtZSlot.`1))
             ((FieldQ.asint newAggregateAtZSlot.`2)) p mem0)
               AGGREGATED_OPENING_AT_Z_SLOT aggregatedOpeningAtZ{1})%PurePrimops /\
         aggregatedAtZSlot{2} =
         ((FieldQ.asint newAggregateAtZSlot.`1),
           (FieldQ.asint newAggregateAtZSlot.`2))
       ).
           inline mload. wp. skip. progress.
           case H.
           progress. left. progress.
           progress. right. progress.

           rewrite /UpdateAggregationChallenge_footprint /STATE_U_SLOT /AGGREGATED_OPENING_AT_Z_SLOT /AGGREGATED_AT_Z_X_SLOT /AGGREGATED_AT_Z_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /addmod /mulmod. simplify.
           do 14! (rewrite load_store_diff; progress).
           rewrite -Constants.R_int of_uintK of_uintK Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. rewrite /Constants.R. progress.
           rewrite Utils.mod_mod_eq_mod. rewrite /Constants.R. progress. rewrite /Constants.R. progress.
           smt (@IntDiv).

           exists x y newAggregateAtZSlot p. progress.
       
      
       (* print modzDmr. *)
       (* print modzDm. *)
       (* print modzMm. *)
