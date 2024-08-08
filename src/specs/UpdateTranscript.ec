require import AllCore.
require import List.
require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

(* Layout
   BEGIN_SLOT     = 3 bytes  [0x0 - 0x2]
   DST_SLOT       = 1 byte   [0x03]
   STATE0_SLOT    = 32 bytes [0x04     - 0x23 (35)] 31
   STATE1_SLOT    = 32 bytes [0x24(36) - 0x43 (67)] 31
   CHALLANGE_SLOT = 32 bytes [0x44(68) - 0x64(100)] 31
*)

op keccakI : int list -> int.

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

  proc mid(tS0 tS1 tC : int) : int * int = {
    var state0, state1 : int;
    state0 <- keccakI [0; tS0; tS1; tC];
    state1 <- keccakI [1; tS0; tS1; tC];
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

axiom keccak256_transcript_dst0_pspec (m: mem) (s0 s1 ch : uint256):
    (W32u8.unpack8(mload m TRANSCRIPT_DST_BYTE_SLOT)).[31] = W8.of_int 0 /\
    mload m TRANSCRIPT_STATE_0_SLOT = s0 /\
    mload m TRANSCRIPT_STATE_1_SLOT = s1 /\
    mload m TRANSCRIPT_CHALLENGE_SLOT = ch =>
    W256.to_uint (PurePrimops.keccak256_f(Array.offun
      (fun (i: int) => m.[TRANSCRIPT_BEGIN_SLOT + (W256.of_int i)]) 100)) =
    keccakI [0; W256.to_uint s0; W256.to_uint s1; W256.to_uint ch].

axiom keccak256_transcript_dst1_pspec (m: mem) (s0 s1 ch : uint256):
    (W32u8.unpack8(mload m TRANSCRIPT_DST_BYTE_SLOT)).[31] = W8.of_int 1 /\
    mload m TRANSCRIPT_STATE_0_SLOT = s0 /\
    mload m TRANSCRIPT_STATE_1_SLOT = s1 /\
    mload m TRANSCRIPT_CHALLENGE_SLOT = ch =>
    W256.to_uint (PurePrimops.keccak256_f(Array.offun
      (fun (i: int) => m.[TRANSCRIPT_BEGIN_SLOT + (W256.of_int i)]) 100)) =
    keccakI [1; W256.to_uint s0; W256.to_uint s1; W256.to_uint ch].
  
lemma updateTranscript_low_equiv_mid (m : mem) (
      transcriptBeginG
      transcriptState0G
      transcriptState1G
      transcriptChallangeG: int
) :
equiv [UpdateTranscript.low ~ UpdateTranscript.mid :
arg{1} = W256.of_int transcriptChallangeG /\
arg{2} = (transcriptState0G, transcriptState1G, transcriptChallangeG) /\
Primops.memory{1} = m /\
!Primops.reverted{1} /\
W256.to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
W256.to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
W256.to_uint (mload m TRANSCRIPT_CHALLENGE_SLOT) = transcriptChallangeG
==>
!Primops.reverted{1} /\
Primops.memory{1} = updateTranscript_memory_footprint m
   (W256.of_int transcriptChallangeG)
   (W256.of_int res{2}.`1)
   (W256.of_int res{2}.`2)
].
proof. proc.
pose m1 := store8 m TRANSCRIPT_DST_BYTE_SLOT W256.zero.
seq 1 0: (
  value{1} = (of_int transcriptChallangeG)%W256 /\
  (tS0{2}, tS1{2}, tC{2}) =
  (transcriptState0G, transcriptState1G, transcriptChallangeG) /\
  !Primops.reverted{1} /\
  to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
  to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
  to_uint (mload m TRANSCRIPT_CHALLENGE_SLOT) = transcriptChallangeG /\
  Primops.memory{1} = m1
).
call{1} (ConcretePrimops.mstore8_pspec m TRANSCRIPT_DST_BYTE_SLOT W256.zero).
skip. by progress.
pose m2 := store m1 TRANSCRIPT_CHALLENGE_SLOT (of_int transcriptChallangeG)%W256.
seq 1 0: (
  value{1} = (of_int transcriptChallangeG)%W256 /\
  (tS0{2}, tS1{2}, tC{2}) =
  (transcriptState0G, transcriptState1G, transcriptChallangeG) /\
  !Primops.reverted{1} /\
  to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
  to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
  to_uint (mload m TRANSCRIPT_CHALLENGE_SLOT) = transcriptChallangeG /\
  Primops.memory{1} = m2
).
call{1} (ConcretePrimops.mstore_pspec m1 TRANSCRIPT_CHALLENGE_SLOT (of_int transcriptChallangeG)%W256).
skip. by progress. 

seq 1 1: (#pre /\
  to_uint newState0{1} = state0{2} /\
  state0{2} = keccakI [0; tS0{2}; tS1{2}; tC{2}]).
call{1} (ConcretePrimops.keccak256_pspec TRANSCRIPT_BEGIN_SLOT (W256.of_int 100)).
wp. skip. progress.
apply keccak256_transcript_dst0_pspec. progress.
rewrite /m2 /m1 load_store_diff /TRANSCRIPT_DST_BYTE_SLOT /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
rewrite load_store8_same. smt().
rewrite /m2 /m1. rewrite load_store_diff.
rewrite /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_CHALLENGE_SLOT. by progress.
rewrite /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_CHALLENGE_SLOT. by progress.
apply load_store8_diff. rewrite /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_DST_BYTE_SLOT. smt().
rewrite /m2 /m1 load_store_diff /TRANSCRIPT_STATE_1_SLOT /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
apply load_store8_diff. rewrite /TRANSCRIPT_DST_BYTE_SLOT. smt().
rewrite /m2 /m1 load_store_same. smt().

pose m3 := store8 m2 TRANSCRIPT_DST_BYTE_SLOT W256.one.
seq 1 0: (
  value{1} = (of_int transcriptChallangeG)%W256 /\
   (tS0{2}, tS1{2}, tC{2}) =
   (transcriptState0G, transcriptState1G, transcriptChallangeG) /\
   !Primops.reverted{1} /\
   to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
   to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
   to_uint (mload m TRANSCRIPT_CHALLENGE_SLOT) = transcriptChallangeG /\
  to_uint newState0{1} = state0{2} /\
  state0{2} = keccakI [0; tS0{2}; tS1{2}; tC{2}] /\
  Primops.memory{1} = m3
).
call{1} (ConcretePrimops.mstore8_pspec m2 TRANSCRIPT_DST_BYTE_SLOT W256.one).
skip. by progress.

seq 1 1: (#pre /\
  to_uint newState1{1} = state1{2} /\
  state1{2} = keccakI [1; tS0{2}; tS1{2}; tC{2}]).
call{1} (ConcretePrimops.keccak256_pspec TRANSCRIPT_BEGIN_SLOT (W256.of_int 100)).
wp. skip. progress.
apply keccak256_transcript_dst1_pspec. progress.
rewrite /m3 /m2 /m1 load_store8_same. smt().
rewrite /m3 /m2 /m1 load_store8_diff /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_DST_BYTE_SLOT. smt().
rewrite load_store_diff /TRANSCRIPT_CHALLENGE_SLOT. by progress. by progress.
rewrite load_store8_diff; smt().
rewrite /m3 /m2 /m1 load_store8_diff /TRANSCRIPT_STATE_1_SLOT /TRANSCRIPT_DST_BYTE_SLOT. smt().
rewrite load_store_diff /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
rewrite load_store8_diff; smt().
rewrite /m3 /m2 /m1 load_store8_diff /TRANSCRIPT_CHALLENGE_SLOT /TRANSCRIPT_DST_BYTE_SLOT. smt().
rewrite load_store_same. smt().

exists* newState1{1}. elim*=> ns1.
pose m4 := store m3 TRANSCRIPT_STATE_1_SLOT ns1.
seq 1 0:(
  ns1 = newState1{1} /\  
  value{1} = (of_int transcriptChallangeG)%W256 /\
   (tS0{2}, tS1{2}, tC{2}) =
   (transcriptState0G, transcriptState1G, transcriptChallangeG) /\
   !Primops.reverted{1} /\
   to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
   to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
   to_uint (mload m TRANSCRIPT_CHALLENGE_SLOT) = transcriptChallangeG /\
   to_uint newState0{1} = state0{2} /\
   state0{2} = keccakI [0; tS0{2}; tS1{2}; tC{2}] /\
  to_uint newState1{1} = state1{2} /\
   state1{2} = keccakI [1; tS0{2}; tS1{2}; tC{2}] /\
   Primops.memory{1} = m4
).
call{1} (ConcretePrimops.mstore_pspec m3 TRANSCRIPT_STATE_1_SLOT ns1).
skip. by progress.

exists* newState0{1}. elim*=> ns0.
pose m5 := store m4 TRANSCRIPT_STATE_0_SLOT ns0.
seq 1 0:(
  ns1 = newState1{1} /\ ns0 = newState0{1} /\  
  value{1} = (of_int transcriptChallangeG)%W256 /\
   (tS0{2}, tS1{2}, tC{2}) =
   (transcriptState0G, transcriptState1G, transcriptChallangeG) /\
   !Primops.reverted{1} /\
   to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
   to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G /\
   to_uint (mload m TRANSCRIPT_CHALLENGE_SLOT) = transcriptChallangeG /\
   to_uint newState0{1} = state0{2} /\
   state0{2} = keccakI [0; tS0{2}; tS1{2}; tC{2}] /\
  to_uint newState1{1} = state1{2} /\
   state1{2} = keccakI [1; tS0{2}; tS1{2}; tC{2}] /\
   Primops.memory{1} = m5
).
call{1} (ConcretePrimops.mstore_pspec m4 TRANSCRIPT_STATE_0_SLOT ns0).
skip. by progress.

skip. by progress.
qed.
