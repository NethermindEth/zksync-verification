require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module UpdateTranscript = {
  proc low(value : uint256): unit = {
    var newState0, newState1;
    Primops.mstore8(TRANSCRIPT_DST_BYTE_SLOT, W256.zero);
    Primops.mstore(TRANSCRIPT_CHALLENGE_SLOT, value);
    newState0 <@ Primops.keccak256(TRANSCRIPT_BEGIN_SLOT, W256.of_int 100);
    Primops.mstore8(TRANSCRIPT_DST_BYTE_SLOT, W256.one);
    newState1 <@ Primops.keccak256(TRANSCRIPT_BEGIN_SLOT, W256.of_int 100);
    Primops.mstore(TRANSCRIPT_STATE_1_SLOT, newState1);
    Primops.mstore(TRANSCRIPT_STATE_0_SLOT, newState0);
  }
}.

lemma updateTranscript_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_updateTranscript ~ UpdateTranscript.low :
      ={arg, glob UpdateTranscript} ==>
      ={res, glob UpdateTranscript}
    ].
proof.
  proc.
  inline*. wp. skip. by progress.
qed.
