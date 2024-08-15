require import AllCore.
require import List.
require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

op keccakTM : int -> int -> int -> int -> int.
op keccakCM : int -> int -> int -> int -> int.

import MemoryMap PurePrimops.

axiom keccak256_transcript_mid (m: mem) (dst s0 s1 ch : int) :
  m.[TRANSCRIPT_DST_BYTE_SLOT] = W8.of_int dst /\
  mload m TRANSCRIPT_STATE_0_SLOT = W256.of_int s0 /\
  mload m TRANSCRIPT_STATE_1_SLOT = W256.of_int s1 /\
  mload m TRANSCRIPT_CHALLENGE_SLOT = W256.of_int ch
  =>
  W256.to_uint (PurePrimops.keccak256_f(Array.offun (fun (i: int) => m.[TRANSCRIPT_BEGIN_SLOT + (W256.of_int i)]) 100)) =
  keccakTM dst s0 s1 ch.

axiom keccak256_challange_mid (m: mem) (dst s0 s1 ch : int):
  m.[TRANSCRIPT_DST_BYTE_SLOT] = W8.of_int dst /\
  mload m TRANSCRIPT_STATE_0_SLOT = W256.of_int s0 /\
  mload m TRANSCRIPT_STATE_1_SLOT = W256.of_int s1 /\
  mload m TRANSCRIPT_CHALLENGE_SLOT = W256.of_int (ch * 2^224)
  =>
  W256.to_uint (PurePrimops.keccak256_f(Array.offun (fun (i: int) => m.[TRANSCRIPT_BEGIN_SLOT + (W256.of_int i)]) 72)) =
  keccakCM dst s0 s1 ch.

(* op keccak_mid = W256.to_uint (keccak_low (cast_args x1 x2 x3 x4)) axiomatiezed by .... *)
  
(* Layout
   BEGIN_SLOT     = 3 bytes  [0x0 - 0x2]
   DST_SLOT       = 1 byte   [0x03]
   STATE0_SLOT    = 32 bytes [0x04     - 0x23 (35)] 31
   STATE1_SLOT    = 32 bytes [0x24(36) - 0x43 (67)] 31
   CHALLANGE_SLOT = 32 bytes [0x44(68) - 0x64(100)] 31
                              0x44     - 0x48          *)

(*             function updateTranscript(value) { *)
(*                 mstore8(TRANSCRIPT_DST_BYTE_SLOT, 0x00) *)
(*                 mstore(TRANSCRIPT_CHALLENGE_SLOT, value) *)
(*                 let newState0 := keccak256(TRANSCRIPT_BEGIN_SLOT, 0x64) *)
(*                 mstore8(TRANSCRIPT_DST_BYTE_SLOT, 0x01) *)
(*                 let newState1 := keccak256(TRANSCRIPT_BEGIN_SLOT, 0x64) *)
(*                 mstore(TRANSCRIPT_STATE_1_SLOT, newState1) *)
(*                 mstore(TRANSCRIPT_STATE_0_SLOT, newState0) *)
(*             } *)

(*             numberOfChallenge \in {0, ... , 10} *)
(*             function getTranscriptChallenge(numberOfChallenge) -> challenge { *)
(*                 mstore8(TRANSCRIPT_DST_BYTE_SLOT, 0x02) *)
(*                 mstore(TRANSCRIPT_CHALLENGE_SLOT, shl(224, numberOfChallenge)) *)
(*                 challenge := and(keccak256(TRANSCRIPT_BEGIN_SLOT, 0x48), FR_MASK) *)
(*             } *)
            
(* updateTranscript(mload(PROOF_PUBLIC_INPUT)) *)
(* updateTranscript(mload(PROOF_STATE_POLYS_0_X_SLOT)) *)
(* updateTranscript(mload(PROOF_STATE_POLYS_0_Y_SLOT)) *)
(* updateTranscript(mload(PROOF_STATE_POLYS_1_X_SLOT)) *)
(* updateTranscript(mload(PROOF_STATE_POLYS_1_Y_SLOT)) *)
(* updateTranscript(mload(PROOF_STATE_POLYS_2_X_SLOT)) *)
(* updateTranscript(mload(PROOF_STATE_POLYS_2_Y_SLOT)) *)
(* updateTranscript(mload(PROOF_STATE_POLYS_3_X_SLOT)) *)
(* updateTranscript(mload(PROOF_STATE_POLYS_3_Y_SLOT)) *)
(* mstore(STATE_ETA_SLOT, getTranscriptChallenge(0)) *)


            
(* 1. keccakI dst s0 s1 ch *)
(* 2. transcript [PROOF_PUBLIC_INPUT]    *)
(*    transcript [PROOF_PUBLIC_INPUT; PROOF_STATE_POLYS_0_X_SLOT]    *)
(*    ...        *)
(*    getChallange (transcript [PROOF_PUBLIC_INPUT; PROOF_STATE_POLYS_0_X_SLOT; ...]) *)
            
(* 3. transcript PROOF_STATE_POLYS_0_X_SLOT (transcript PROOF_PUBLIC_INPUT old) *)
(*    transcript int -> state -> state *)

(* 4. linked list *)

            
(* forall (a : uint8 array), *)
(*    W256.to_uint (keccak_f a) = keccakI (map W8.of_int a) *)

(* 10 bytes *)
(* 0-2 - int *)
                

            
(* forall (a : uint8 array) (l : int list), *)
(*    W256.to_uint (keccak_f a) = keccakI l *)
