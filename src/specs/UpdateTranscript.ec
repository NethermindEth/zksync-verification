require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module UpdateTranscript = {
  proc low(value : uint256): unit = {
    var newState0, newState1;
    Primops.mstore8(W256.of_int 3395, W256.zero);
    Primops.mstore(W256.of_int 3460, value);
    newState0 <@ Primops.keccak256(W256.of_int 3392, W256.of_int 100);
    Primops.mstore8(W256.of_int 3395, W256.one);
    newState1 <@ Primops.keccak256(W256.of_int 3392, W256.of_int 100);
    Primops.mstore(W256.of_int 3428, newState1);
    Primops.mstore(W256.of_int 3396, newState0);
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
