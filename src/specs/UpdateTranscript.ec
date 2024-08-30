pragma Goals:printall.

require import AllCore.
require import List.
require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.
require import Keccak.

(* Layout
   BEGIN_SLOT     = 3 bytes  [0x0 - 0x2]
   DST_SLOT       = 1 byte   [0x03]
   STATE0_SLOT    = 32 bytes [0x04     - 0x23 (35)] 31
   STATE1_SLOT    = 32 bytes [0x24(36) - 0x43 (67)] 31
   CHALLANGE_SLOT = 32 bytes [0x44(68) - 0x64(100)] 31
*)

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
  
  proc mid(tS0 tS1 v : int) : int * int = {
    var state0, state1 : int;
    state0 <- keccakT 0 tS0 tS1 v;
    state1 <- keccakT 1 tS0 tS1 v;
    return (state0, state1);
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

lemma updateTranscript_pspec_revert :
phoare [ UpdateTranscript.low : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; inline*; wp; skip; by auto. qed.

import MemoryMap PurePrimops.

op updateTranscript_memory_footprint (m: mem) (c ks0 ks1 : uint256) : mem =
let m1 = store8 m TRANSCRIPT_DST_BYTE_SLOT W256.zero in
let m2 = store m1 TRANSCRIPT_CHALLENGE_SLOT c in 
let m3 = store8 m2 TRANSCRIPT_DST_BYTE_SLOT W256.one in
let m4 = store m3 TRANSCRIPT_STATE_1_SLOT ks1 in
let m5 = store m4 TRANSCRIPT_STATE_0_SLOT ks0 in
m5.

lemma updateTranscript_memory_footprint_same (m: mem) (a1 a2 b1 b2 c1 c2 : uint256) : 
    updateTranscript_memory_footprint (updateTranscript_memory_footprint m a1 b1 c1) a2 b2 c2 =
    updateTranscript_memory_footprint m a2 b2 c2.
proof.
rewrite /updateTranscript_memory_footprint /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_STATE_1_SLOT /TRANSCRIPT_CHALLENGE_SLOT /TRANSCRIPT_DST_BYTE_SLOT. simplify.
rewrite (store_store_swap_diff _ (W256.of_int 3428) (W256.of_int 3396) _ _); try by simplify.
rewrite (store_store8_swap_diff _ (W256.of_int 3395) (W256.of_int 3396) _ _); try (exists 1; by simplify).
rewrite (store_store_swap_diff _ (W256.of_int 3460) (W256.of_int 3396) _ _); try by simplify.
rewrite (store_store8_swap_diff _ (W256.of_int 3395) (W256.of_int 3396) _ _); try (exists 1; by simplify).
rewrite store_store_same.
rewrite (store_store8_swap_diff _ (W256.of_int 3395) (W256.of_int 3428) _ _); first smt().
rewrite (store_store_swap_diff _ (W256.of_int 3460) (W256.of_int 3428) _ _); try by simplify.
rewrite (store_store8_swap_diff _ (W256.of_int 3395) (W256.of_int 3428) _ _); first smt().
rewrite (store_store_swap_diff _ (W256.of_int 3396) (W256.of_int 3428) _ _); try by simplify.
rewrite store_store_same.
rewrite (store_store8_swap_diff _ (W256.of_int 3395) (W256.of_int 3460) _ _); first smt().
rewrite (store_store_swap_diff _ (W256.of_int 3396) (W256.of_int 3460) _ _); try by simplify.
rewrite (store_store_swap_diff _ (W256.of_int 3428) (W256.of_int 3460) _ _); try by simplify.
rewrite (store_store8_swap_diff _ (W256.of_int 3395) (W256.of_int 3460) _ _); first smt().
rewrite store_store_same.
rewrite store8_store8_same.
rewrite (store_store8_swap_diff _ (W256.of_int 3395) (W256.of_int 3460) _ _); first smt().
rewrite store8_store8_same.
rewrite (store_store8_swap_diff _ (W256.of_int 3395) (W256.of_int 3428) _ _); first smt().
rewrite (store_store8_swap_diff _ (W256.of_int 3395) (W256.of_int 3396) _ _); first smt().
rewrite store8_store8_same.
reflexivity.
qed.

lemma updateTranscript_low_equiv_mid (m : mem) (
      transcriptState0G
      transcriptState1G
      valueG : int
) :
equiv [UpdateTranscript.low ~ UpdateTranscript.mid :
arg{1} = W256.of_int valueG /\
arg{2} = (transcriptState0G, transcriptState1G, valueG) /\
Primops.memory{1} = m /\
!Primops.reverted{1} /\
W256.to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
W256.to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G
==>
!Primops.reverted{1} /\
Primops.memory{1} = updateTranscript_memory_footprint m
   (W256.of_int valueG)
   (W256.of_int res{2}.`1)
   (W256.of_int res{2}.`2) /\
0 <= res{2}.`1 < W256.modulus /\
0 <= res{2}.`2 < W256.modulus
].
proof. proc.
pose m1 := store8 m TRANSCRIPT_DST_BYTE_SLOT W256.zero.
seq 1 0: (
  value{1} = (of_int valueG)%W256 /\
  (tS0{2}, tS1{2}, v{2}) =
  (transcriptState0G, transcriptState1G, valueG) /\
  !Primops.reverted{1} /\
  to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
  to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
  Primops.memory{1} = m1
).
call{1} (ConcretePrimops.mstore8_pspec m TRANSCRIPT_DST_BYTE_SLOT W256.zero).
skip. by progress.
pose m2 := store m1 TRANSCRIPT_CHALLENGE_SLOT (of_int valueG)%W256.
seq 1 0: (
  value{1} = (of_int valueG)%W256 /\
  (tS0{2}, tS1{2}, v{2}) =
  (transcriptState0G, transcriptState1G, valueG) /\
  !Primops.reverted{1} /\
  to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
  to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
  Primops.memory{1} = m2
).
call{1} (ConcretePrimops.mstore_pspec m1 TRANSCRIPT_CHALLENGE_SLOT (of_int valueG)%W256).
skip. by progress. 

seq 1 1: (#pre /\
  to_uint newState0{1} = state0{2} /\
  state0{2} = keccakT 0 tS0{2} tS1{2} v{2} /\ 0 <= state0{2} < W256.modulus).
wp. call{1} (keccak256_pspec_transcript m2 0 transcriptState0G transcriptState1G valueG).
skip. progress.
rewrite /m2 /m1 load8_store_diff /TRANSCRIPT_DST_BYTE_SLOT /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
rewrite load8_store8_same. by progress.
rewrite /m2 /m1 load_store_diff /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
rewrite load_store8_diff /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_DST_BYTE_SLOT; smt().
rewrite /m2 /m1 load_store_diff /TRANSCRIPT_STATE_1_SLOT /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
rewrite load_store8_diff /TRANSCRIPT_DST_BYTE_SLOT; smt().
rewrite /m2 /m1 load_store_same; reflexivity.

pose m3 := store8 m2 TRANSCRIPT_DST_BYTE_SLOT W256.one.
seq 1 0: (
  value{1} = (of_int valueG)%W256 /\
   (tS0{2}, tS1{2}, v{2}) = (transcriptState0G, transcriptState1G, valueG) /\
   !Primops.reverted{1} /\
   to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
   to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
  to_uint newState0{1} = state0{2} /\
  state0{2} = keccakT 0 tS0{2} tS1{2} v{2} /\ 0 <= state0{2} < W256.modulus /\
  Primops.memory{1} = m3
).
call{1} (ConcretePrimops.mstore8_pspec m2 TRANSCRIPT_DST_BYTE_SLOT W256.one).
skip. by progress.

seq 1 1: (#pre /\
  to_uint newState1{1} = state1{2} /\
  state1{2} = keccakT 1 tS0{2} tS1{2} v{2} /\ 0 <= state1{2} < W256.modulus).
wp. call{1} (keccak256_pspec_transcript m3 1 transcriptState0G transcriptState1G valueG).
skip. progress.
rewrite /m3 /m2 /m1 load8_store8_same. by progress.
rewrite /m3 /m2 /m1 load_store8_diff /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_DST_BYTE_SLOT; first smt().
rewrite load_store_diff /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
rewrite load_store8_diff; first smt(); try by progress. reflexivity.
rewrite /m3 /m2 /m1 load_store8_diff /TRANSCRIPT_STATE_1_SLOT /TRANSCRIPT_DST_BYTE_SLOT; first smt().
rewrite load_store_diff /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
rewrite load_store8_diff; smt().
rewrite /m3 /m2 /m1 load_store8_diff /TRANSCRIPT_CHALLENGE_SLOT /TRANSCRIPT_DST_BYTE_SLOT; first smt().
rewrite load_store_same; smt().

exists* newState1{1}. elim*=> ns1.
pose m4 := store m3 TRANSCRIPT_STATE_1_SLOT ns1.
seq 1 0:(
  ns1 = newState1{1} /\  
  value{1} = (of_int valueG)%W256 /\
   (tS0{2}, tS1{2}, v{2}) = (transcriptState0G, transcriptState1G, valueG) /\
   !Primops.reverted{1} /\
   to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
   to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
   to_uint newState0{1} = state0{2} /\
   state0{2} = keccakT 0 tS0{2} tS1{2} v{2} /\ 0 <= state0{2} < W256.modulus /\
  to_uint newState1{1} = state1{2} /\
  state1{2} = keccakT 1 tS0{2} tS1{2} v{2} /\ 0 <= state1{2} < W256.modulus /\
   Primops.memory{1} = m4
).
call{1} (ConcretePrimops.mstore_pspec m3 TRANSCRIPT_STATE_1_SLOT ns1).
skip. by progress.

exists* newState0{1}. elim*=> ns0.
pose m5 := store m4 TRANSCRIPT_STATE_0_SLOT ns0.
seq 1 0:(
  ns1 = newState1{1} /\ ns0 = newState0{1} /\  
  value{1} = (of_int valueG)%W256 /\
  (tS0{2}, tS1{2}, v{2}) = (transcriptState0G, transcriptState1G, valueG) /\
  !Primops.reverted{1} /\
  to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
  to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
  to_uint newState0{1} = state0{2} /\
  state0{2} = keccakT 0 tS0{2} tS1{2} v{2} /\ 0 <= state0{2} < W256.modulus /\
  to_uint newState1{1} = state1{2} /\
  state1{2} = keccakT 1 tS0{2} tS1{2} v{2} /\ 0 <= state1{2} < W256.modulus /\
   Primops.memory{1} = m5
).
call{1} (ConcretePrimops.mstore_pspec m4 TRANSCRIPT_STATE_0_SLOT ns0).
skip. by progress.
skip. by progress.
qed.
