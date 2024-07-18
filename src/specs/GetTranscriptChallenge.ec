require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module GetTranscriptChallenge = {
  proc low(numberOfChallenge : uint256): uint256 = {
    var challenge, _6, _9;
    Primops.mstore8(TRANSCRIPT_DST_BYTE_SLOT, W256.of_int 2);
    Primops.mstore(TRANSCRIPT_CHALLENGE_SLOT, PurePrimops.shl (W256.of_int 224) numberOfChallenge);
    _6 <- ((PurePrimops.shl (W256.of_int 253) (W256.of_int 1)) - (W256.of_int 1));
    _9 <@ Primops.keccak256(TRANSCRIPT_BEGIN_SLOT, W256.of_int 72);
    challenge <- (PurePrimops.bit_and _9 _6);
    return challenge;
    }
}.

lemma getTranscriptChallenge_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_getTranscriptChallenge ~ GetTranscriptChallenge.low :
      ={arg, glob GetTranscriptChallenge} ==>
      ={res, glob GetTranscriptChallenge}
    ].
proof.
  proc.
  inline*. wp. skip. by progress.
qed.
