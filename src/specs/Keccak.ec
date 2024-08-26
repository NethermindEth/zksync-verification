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
   CHALLANGE_SLOT = 32 bytes [0x44(68) - 0x64(100)] 31 *)

op keccakTM : int -> int -> int -> int -> int.
op keccakCM : int -> int -> int -> int -> int.

import MemoryMap PurePrimops.

axiom keccak256_transcript_mid (m: mem) (dst s0 s1 ch : int) :
  m.[TRANSCRIPT_DST_BYTE_SLOT] = W8.of_int dst /\
  mload m TRANSCRIPT_STATE_0_SLOT = W256.of_int s0 /\
  mload m TRANSCRIPT_STATE_1_SLOT = W256.of_int s1 /\
  mload m TRANSCRIPT_CHALLENGE_SLOT = W256.of_int ch
  =>
  ((W256.to_uint (PurePrimops.keccak256_f(Array.offun (fun (i: int) => m.[TRANSCRIPT_BEGIN_SLOT + (W256.of_int i)]) 100)) =
  keccakTM dst s0 s1 ch) /\
  0 <= keccakTM dst s0 s1 ch < W256.modulus).

lemma keccak256_pspec_transcript (m: mem) (dst s0 s1 ch: int):
    phoare [ Primops.keccak256 :
      arg = (TRANSCRIPT_BEGIN_SLOT, (of_int 100)%W256) /\
      Primops.memory = m /\
      m.[TRANSCRIPT_DST_BYTE_SLOT] = W8.of_int dst /\
      mload m TRANSCRIPT_STATE_0_SLOT = W256.of_int s0 /\
      mload m TRANSCRIPT_STATE_1_SLOT = W256.of_int s1 /\
      mload m TRANSCRIPT_CHALLENGE_SLOT = W256.of_int ch
      ==>
      W256.to_uint res = keccakTM dst s0 s1 ch /\
      0 <= keccakTM dst s0 s1 ch < W256.modulus
    ] = 1%r.
proof. proc.
wp. skip. move=> &hr [[]] ? ? [] ? H. subst.
have k: m.[TRANSCRIPT_DST_BYTE_SLOT] = W8.of_int dst /\
  mload m TRANSCRIPT_STATE_0_SLOT = W256.of_int s0 /\
  mload m TRANSCRIPT_STATE_1_SLOT = W256.of_int s1 /\
  mload m TRANSCRIPT_CHALLENGE_SLOT = W256.of_int ch
  =>
  ((W256.to_uint (PurePrimops.keccak256_f(Array.offun (fun (i: int) => m.[TRANSCRIPT_BEGIN_SLOT + (W256.of_int i)]) 100)) =
  keccakTM dst s0 s1 ch) /\
  0 <= keccakTM dst s0 s1 ch < W256.modulus).
apply keccak256_transcript_mid. apply k. auto.
qed.

axiom keccak256_challange_mid (m: mem) (dst s0 s1 ch : int):
  m.[TRANSCRIPT_DST_BYTE_SLOT] = W8.of_int dst /\
  mload m TRANSCRIPT_STATE_0_SLOT = W256.of_int s0 /\
  mload m TRANSCRIPT_STATE_1_SLOT = W256.of_int s1 /\
  mload m TRANSCRIPT_CHALLENGE_SLOT = W256.of_int (ch * 2^224)
  =>
  W256.to_uint (PurePrimops.keccak256_f(Array.offun (fun (i: int) => m.[TRANSCRIPT_BEGIN_SLOT + (W256.of_int i)]) 72)) =
  keccakCM dst s0 s1 ch /\
  0 <= keccakCM dst s0 s1 ch < W256.modulus.

lemma keccak256_pspec_challange (m: mem) (dst s0 s1 ch: int):
    phoare [ Primops.keccak256 :
      arg = (TRANSCRIPT_BEGIN_SLOT, (of_int 72)%W256) /\
      Primops.memory = m /\
      m.[TRANSCRIPT_DST_BYTE_SLOT] = W8.of_int dst /\
      mload m TRANSCRIPT_STATE_0_SLOT = W256.of_int s0 /\
      mload m TRANSCRIPT_STATE_1_SLOT = W256.of_int s1 /\
      mload m TRANSCRIPT_CHALLENGE_SLOT = W256.of_int (ch * 2^224)
      ==>
      W256.to_uint res = keccakCM dst s0 s1 ch /\
      0 <= keccakCM dst s0 s1 ch < W256.modulus
    ] = 1%r.
proof. proc.
wp. skip. move=> &hr [[]] ? ? [] ? H. subst.
have k: m.[TRANSCRIPT_DST_BYTE_SLOT] = W8.of_int dst /\
  mload m TRANSCRIPT_STATE_0_SLOT = W256.of_int s0 /\
  mload m TRANSCRIPT_STATE_1_SLOT = W256.of_int s1 /\
  mload m TRANSCRIPT_CHALLENGE_SLOT = W256.of_int (ch * 2^224)
  =>
  ((W256.to_uint (PurePrimops.keccak256_f(Array.offun (fun (i: int) => m.[TRANSCRIPT_BEGIN_SLOT + (W256.of_int i)]) 72)) =
  keccakCM dst s0 s1 ch) /\
  0 <= keccakCM dst s0 s1 ch < W256.modulus).
apply keccak256_challange_mid. apply k. auto.
qed.
