pragma Goals:printall.

require        Constants.
require import IntDiv.
require import Memory.
require import PurePrimops.
require import Ring.
        import Ring.IntID.
require import UInt256.
require import Verifier.
require import YulPrimops.

import MemoryMap.

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
      Verifier_1261.usr_revertWithMessage(W256.of_int 24, W256.of_int STRING);
    }

    ret <@ Primops.mload(W256.zero);
    return ret;
  }

  proc mid(value: int, power: int): int = {
    return (value ^ power) %% Constants.R;
  }
}.

lemma modexp_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_modexp ~ Modexp.low :
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

op modexp_memory_footprint (memory: mem) (value power result: uint256) =
  let mem_1 = store memory W256.zero         result in
  let mem_2 = store mem_1  (W256.of_int 32)  (W256.of_int 32) in
  let mem_3 = store mem_2  (W256.of_int 64)  (W256.of_int 32) in
  let mem_4 = store mem_3  (W256.of_int 96)  value in
  let mem_5 = store mem_4  (W256.of_int 128) power in
  let mem_6 = store mem_5  (W256.of_int 160) (W256.of_int Constants.R) in
  mem_6.
  
lemma modexp_low_equiv_mid (memory: mem) (value256 power256: uint256):
    equiv [
      Modexp.low ~ Modexp.mid:
      arg{1} = (value256, power256) /\
      arg{2} = (W256.to_uint value256, W256.to_uint power256) /\
      !Primops.reverted{1} /\
      Primops.memory{1} = memory    
      ==>
      res{2} = W256.to_uint res{1} /\
      0 <= res{2} < Constants.R /\
      !Primops.reverted{1} /\
      Primops.memory{1} = (modexp_memory_footprint memory value256 power256 res{1})
    ].
proof.
    proc.
    (* work down to the staticcall *)
    pose mem_1 := PurePrimops.mstore memory W256.zero (W256.of_int 32).
    pose mem_2 := PurePrimops.mstore mem_1 (W256.of_int 32) (W256.of_int 32).
    pose mem_3 := PurePrimops.mstore mem_2 (W256.of_int 64) (W256.of_int 32).
    pose mem_4 := PurePrimops.mstore mem_3 (W256.of_int 96) value256.
    pose mem_5 := PurePrimops.mstore mem_4 (W256.of_int 128) power256.
    pose mem_6 := PurePrimops.mstore mem_5 (W256.of_int 160) (W256.of_int Constants.R).
    have H_mem6_get0: PurePrimops.mload mem_6 W256.zero = W256.of_int 32.
    do 5! ((rewrite load_store_diff; first smt(@W256)); first smt(@W256)).
    rewrite load_store_same. reflexivity.
    have H_mem6_get32: PurePrimops.mload mem_6 (W256.of_int 32) = W256.of_int 32.
    do 4! ((rewrite load_store_diff; first smt(@W256)); first smt(@W256)).
    rewrite load_store_same. reflexivity.
    have H_mem6_get64: PurePrimops.mload mem_6 (W256.of_int 64) = W256.of_int 32.
    do 3! ((rewrite load_store_diff; first smt(@W256)); first smt(@W256)).
    rewrite load_store_same. reflexivity.
    have H_mem6_get96: PurePrimops.mload mem_6 (W256.of_int 96) = value256.
    do 2! ((rewrite load_store_diff; first smt(@W256)); first smt(@W256)).
    rewrite load_store_same. reflexivity.
    have H_mem6_get128: PurePrimops.mload mem_6 (W256.of_int 128) = power256.
    rewrite load_store_diff. smt(@W256). smt(@W256).
    rewrite load_store_same. reflexivity.
    have H_mem6_get160: PurePrimops.mload mem_6 (W256.of_int 160) = (W256.of_int Constants.R).
    rewrite load_store_same. reflexivity.
    seq 6 0: (Primops.memory{1} = mem_6 /\ !Primops.reverted{1} /\ value{2} = W256.to_uint value256 /\ power{2} = W256.to_uint power256).
    inline*. wp. skip. by progress.
    inline Primops.gas. sp.
    (* work up to the staticcall *)
    pose mem_7 := PurePrimops.mstore mem_6 W256.zero (PurePrimops.modexp value256 power256 (W256.of_int Constants.R)).
    have H_mem7_get0: PurePrimops.mload mem_7 W256.zero = (PurePrimops.modexp value256 power256 (W256.of_int Constants.R)) by smt(@MemoryMap).
    call{1} (ConcretePrimops.mload_pspec mem_7 W256.zero).
    rcondf{1} 2. progress. inline*. wp. skip. progress. smt(@PurePrimops). smt(@PurePrimops).
    exists* gas{1}.
    elim* => gas.
    call{1} (ConcretePrimops.staticcall_modexp_pspec mem_6 value256 power256 (W256.of_int Constants.R) gas W256.zero W256.zero).
    skip. progress.
    rewrite H_mem7_get0 PurePrimops.modexpE.
      rewrite W256.of_uintK.
      (*ltz_pmod*)
      (*pmod_small*)
    rewrite W256.of_uintK.
    rewrite (pmod_small _ W256.modulus).
    by smt.
    rewrite (pmod_small _ W256.modulus). by smt ().
    by reflexivity.
    by smt().
    by smt().
    rewrite /modexp_memory_footprint. simplify.
      rewrite /mem_6 /mem_5 /mem_4 /mem_3 /mem_2 /mem_1.
      do 5! (rewrite MemoryMap.store_store_swap_diff; [smt (@W256) | smt (@W256) | congr]).
      rewrite MemoryMap.store_store_same. congr.
      rewrite H_mem7_get0.
      reflexivity.
    qed.
    
