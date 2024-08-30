require import AllCore.
require import FinalPairing.
require import InitializeTranscript.
require import LoadProof.
require import LoadVerificationKey.
require import PrepareAggregatedCommitment.
require import PrepareQueries.
require import PurePrimops.
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


lemma verify_failure_pspec :
    phoare [ Verify.low :      
      !on_curve_int (point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product) \/
      !on_curve_int (point_to_uint PurePrimops.load_calldata_lookup_s_poly) \/
      !on_curve_int (point_to_uint PurePrimops.load_calldata_lookup_grand_product) \/
      !on_curve_int (point_to_uint PurePrimops.load_calldata_quotient_poly_part_0) \/
      !on_curve_int (point_to_uint PurePrimops.load_calldata_quotient_poly_part_1) \/
      !on_curve_int (point_to_uint PurePrimops.load_calldata_quotient_poly_part_2) \/
      !on_curve_int (point_to_uint PurePrimops.load_calldata_quotient_poly_part_3) \/
      !on_curve_int (point_to_uint PurePrimops.load_calldata_opening_proof_at_z) \/
      !on_curve_int (point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega) \/
      !on_curve_int (point_to_uint PurePrimops.load_calldata_recursive_part_p1) \/
      !on_curve_int (point_to_uint PurePrimops.load_calldata_recursive_part_p2)
      ==>
      Primops.reverted
    ] = 1%r.
    proof.
      proc.
      seq 1 : (#pre).
      inline*. wp. skip. progress.
      inline*. wp. skip. progress.
      inline LoadProof.low.
      
