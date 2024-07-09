require import UInt256.
require import PurePrimops.
require import Real.
require import Verifier.
require import YulPrimops.

module RevertWithMessage = {
  proc low(len : uint256, reason : uint256): unit = {
    Primops.mstore(W256.zero, PurePrimops.shl (W256.of_int 229) (W256.of_int 4594637));
    Primops.mstore(W256.of_int 4, W256.of_int 32);
    Primops.mstore(W256.of_int 36, len);
    Primops.mstore(W256.of_int 68, reason);
    Primops.revert(W256.zero, W256.of_int 100);
  }
}.

lemma revertWithMessage_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_revertWithMessage ~ RevertWithMessage.low :
      ={arg, glob RevertWithMessage} ==>
      ={res, glob RevertWithMessage}
    ].
        proc.
        inline *.
        wp.
        skip.
        by progress.
    qed.

lemma revertWithMessage_low_pspec:
    phoare [
      RevertWithMessage.low:
      true ==>
      Primops.reverted
    ] = 1%r.
    proof.
      proc.
      inline*. wp. skip. by progress.
    qed.
