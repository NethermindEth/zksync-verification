pragma Goals:printall.

require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module Modexp = {
  proc low(value: uint256, power: uint256): uint256 = {
    var gas, staticcall_success, ret;
    Primops.mstore(W256.zero, W256.of_int 32);
    Primops.mstore(W256.of_int 32, W256.of_int 32);
    Primops.mstore(W256.of_int 64, W256.of_int 32);
    Primops.mstore(W256.of_int 96, value);
    Primops.mstore(W256.of_int 128, power);
    Primops.mstore(W256.of_int 160, W256.of_int Constants.R);
    gas <@ Primops.gas();
    staticcall_success <@ Primops.staticcall(gas, W256.of_int 5, W256.zero, W256.of_int 192, W256.zero, W256.of_int 32);
    if (bool_of_uint256 (PurePrimops.iszero staticcall_success))
    {
      Verifier.usr_revertWithMessage(W256.of_int 24, W256.of_int STRING);
    }

    ret <@ Primops.mload(W256.zero);
    return ret;
  }
}.

lemma modexp_extracted_equiv_low:
    equiv [
      Verifier.usr_modexp ~ Modexp.low :
      ={arg, glob Modexp} ==>
      ={res, glob Modexp}
    ].
    proof.
    proc.
    seq 3 1: (#pre /\ _1{1} = W256.of_int 32 /\ _2{1} = W256.zero). inline*. wp. skip. by progress.
    seq 1 1: #pre. inline*. wp. skip. by progress.
    seq 2 1: #pre. inline*. wp. skip. by progress.
    seq 2 1: #pre. inline*. wp. skip. by progress.
    seq 2 1: #pre. inline*. wp. skip. by progress.
    seq 3 1: #pre. inline*. wp. skip. progress. rewrite /Constants.R. by reflexivity.
    seq 4 1: (#pre /\ _8{1} = W256.of_int 192 /\ _9{1} = W256.of_int 5 /\ _10{1} = gas{2}). inline*. wp. skip. by progress.
    seq 1 1: (#pre /\ tmp50{1} = staticcall_success{2}). inline*. wp. skip. by progress.
    inline*. wp. skip. by progress.
qed.



    
