pragma Goals:printall.

require import AllCore.
require import Int.
require import IntDiv.
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

   but its hashed up to 0x48
*)

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

  proc mid(s0 s1 c : int) : int = {
    return (keccakC 2 s0 s1 c) %% 2^253;
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

lemma getTranscriptChallenge_pspec_revert :
phoare [ GetTranscriptChallenge.low : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; inline*; wp; skip; by auto. qed.

import MemoryMap PurePrimops.

op getTranscriptChallenge_memory_footprint (m: mem) (c : int) : mem =
let m1 = store8 m TRANSCRIPT_DST_BYTE_SLOT (W256.of_int 2) in
let m2 = store m1 TRANSCRIPT_CHALLENGE_SLOT (W256.of_int (c * 2^224)) in 
m2.

lemma getTranscriptChallenge_low_equiv_mid (m : mem) (
      transcriptState0G
      transcriptState1G
      numChallangeG : int
) :
equiv [GetTranscriptChallenge.low ~ GetTranscriptChallenge.mid :
arg{1} = W256.of_int numChallangeG /\
arg{2} = (transcriptState0G, transcriptState1G, numChallangeG) /\
Primops.memory{1} = m /\
!Primops.reverted{1} /\
0 <= numChallangeG < 2^32 /\
W256.to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
W256.to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G
==>
!Primops.reverted{1} /\
Primops.memory{1} = getTranscriptChallenge_memory_footprint m numChallangeG /\
W256.to_uint res{1} = res{2} /\
0 <= res{2} < 2^253
].
proof. proc.
pose m1 := store8 m TRANSCRIPT_DST_BYTE_SLOT (W256.of_int 2).
seq 1 0: (
  numberOfChallenge{1} = (of_int numChallangeG)%W256 /\
  (s0{2}, s1{2}, c{2}) =
  (transcriptState0G, transcriptState1G, numChallangeG) /\
  0 <= numChallangeG < 2^32 /\
  Primops.memory{1} = m1 /\
  !Primops.reverted{1} /\
  to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
  to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G
).
call{1} (ConcretePrimops.mstore8_pspec m TRANSCRIPT_DST_BYTE_SLOT (W256.of_int 2)).
skip. by progress.

pose m2 := store m1 TRANSCRIPT_CHALLENGE_SLOT (W256.of_int (numChallangeG * 2^224)).
seq 1 0: (
  numberOfChallenge{1} = (of_int numChallangeG)%W256 /\
  (s0{2}, s1{2}, c{2}) =
  (transcriptState0G, transcriptState1G, numChallangeG) /\
  0 <= numChallangeG < 2^32 /\
  Primops.memory{1} = m2 /\
  !Primops.reverted{1} /\
  to_uint (mload m TRANSCRIPT_STATE_0_SLOT) = transcriptState0G /\
  to_uint (mload m TRANSCRIPT_STATE_1_SLOT) = transcriptState1G
).
call{1} (ConcretePrimops.mstore_pspec m1 TRANSCRIPT_CHALLENGE_SLOT (W256.of_int (numChallangeG * 2^224))).
skip. progress. rewrite /shl shlMP. smt(@W256). smt(@W256).

seq 1 0: (#pre /\ W256.to_uint _6{1} = 2^253 - 1 /\ _6{1} = VerifierConsts.FR_MASK).
wp. skip. progress; rewrite /shl /FR_MASK shlMP; smt(@W256).

seq 1 0: (#pre /\ to_uint _9{1} = keccakC 2 s0{2} s1{2} c{2}).
call {1} (keccak256_pspec_challange m2 2 transcriptState0G transcriptState1G numChallangeG).
skip; progress.
rewrite /m2 /m1 load8_store_diff /TRANSCRIPT_DST_BYTE_SLOT /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
rewrite load8_store8_same. by progress.
rewrite /m2 /m1 load_store_diff /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
rewrite load_store8_diff /TRANSCRIPT_STATE_0_SLOT /TRANSCRIPT_DST_BYTE_SLOT; smt().
rewrite /m2 /m1 load_store_diff /TRANSCRIPT_STATE_1_SLOT /TRANSCRIPT_CHALLENGE_SLOT; try by progress.
rewrite load_store8_diff /TRANSCRIPT_DST_BYTE_SLOT; smt().
rewrite /m2 /m1 load_store_same; reflexivity.

wp. skip. progress. rewrite /bit_and. 
have ->: FR_MASK = W256.of_int (2^253 - 1). by smt(@W256).
rewrite and_mod. by auto. smt(@W256). smt(@W256). smt(@W256).
qed.
