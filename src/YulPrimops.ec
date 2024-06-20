pragma Goals:printall.

require import Logic Array.
require import Utils.
require export UInt256 Memory.
op calldata : uint256 array.
op keccak256_f : uint256 array -> uint256.

op iszero(v : uint256) : uint256 = if (v = W256.zero) then W256.one else  W256.zero.
lemma iszero_zeroE : iszero (W256.zero) = W256.one.
    proof.
      rewrite /iszero.
      simplify.
      trivial.
  qed.
lemma iszero_nonzeroE : forall (val: uint256), val <> W256.zero => iszero val = W256.zero.
    proof.
      progress.
      rewrite /iszero.
      smt.
    qed.
    
op mulmod(a b n : uint256) : uint256 =  (a * b) %% n
axiomatized by mulmodE.

op addmod(a b n : uint256) : uint256 = (a + b) %% n
axiomatized by addmodE.

op bit_and(a : uint256, b : uint256) : uint256 = a `&` b
axiomatized by bit_andE.

op shl(a : uint256, b : uint256) : uint256 = a `<<<` (W256.to_uint b)
axiomatized by shlE.

op shr(a : uint256, b : uint256) : uint256 = a `>>>` (W256.to_uint b)
axiomatized by shrE.

op STRING : uint256 = W256.zero.

module Primops = {
  var memory : mem
  var reverted : bool

  proc mload(idx : uint256) : uint256 = {
    (* _1 is the most significant byte *)
    (* TODO replace definition with a direct call to op mload *)
    var _r1, _r2, _r3, _r4, _r5, _r6, _r7, _r8, _r9, _r10, _r11, _r12, _r13, _r14, _r15, _r16, _r17, _r18, _r19, _r20, _r21, _r22, _r23, _r24, _r25, _r26, _r27, _r28, _r29, _r30, _r31, _r32;


    _r1 <- memory.[idx] `<<<` 248;
    _r2 <- memory.[idx+ W256.of_int 1] `<<<` 240;
    _r3 <- memory.[idx+ W256.of_int 2] `<<<` 232;
    _r4 <- memory.[idx+ W256.of_int 3] `<<<` 224;
    _r5 <- memory.[idx+ W256.of_int 4] `<<<` 216;
    _r6 <- memory.[idx+ W256.of_int 5] `<<<` 208;
    _r7 <- memory.[idx+ W256.of_int 6] `<<<` 200;
    _r8 <- memory.[idx+ W256.of_int 7] `<<<` 192;
    _r9 <- memory.[idx+ W256.of_int 8] `<<<` 184;
    _r10 <- memory.[idx+ W256.of_int 9] `<<<` 176;
    _r11 <- memory.[idx+ W256.of_int 10] `<<<` 168;
    _r12 <- memory.[idx+ W256.of_int 11] `<<<` 160;
    _r13 <- memory.[idx+ W256.of_int 12] `<<<` 152;
    _r14 <- memory.[idx+ W256.of_int 13] `<<<` 144;
    _r15 <- memory.[idx+ W256.of_int 14] `<<<` 136;
    _r16 <- memory.[idx+ W256.of_int 15] `<<<` 128;
    _r17 <- memory.[idx+ W256.of_int 16] `<<<` 120;
    _r18 <- memory.[idx+ W256.of_int 17] `<<<` 112;
    _r19 <- memory.[idx+ W256.of_int 18] `<<<` 104;
    _r20 <- memory.[idx+ W256.of_int 19] `<<<` 96;
    _r21 <- memory.[idx+ W256.of_int 20] `<<<` 88;
    _r22 <- memory.[idx+ W256.of_int 21] `<<<` 80;
    _r23 <- memory.[idx+ W256.of_int 22] `<<<` 72;
    _r24 <- memory.[idx+ W256.of_int 23] `<<<` 64;
    _r25 <- memory.[idx+ W256.of_int 24] `<<<` 56;
    _r26 <- memory.[idx+ W256.of_int 25] `<<<` 48;
    _r27 <- memory.[idx+ W256.of_int 26] `<<<` 40;
    _r28 <- memory.[idx+ W256.of_int 27] `<<<` 32;
    _r29 <- memory.[idx+ W256.of_int 28] `<<<` 24;
    _r30 <- memory.[idx+ W256.of_int 29] `<<<` 16;
    _r31 <- memory.[idx+ W256.of_int 30] `<<<` 8;
    _r32 <- memory.[idx+ W256.of_int 31];

    return (
      _r32 +
      _r31 +
      _r30 +
      _r29 +
      _r28 +
      _r27 +
      _r26 +
      _r25 +
      _r24 +
      _r23 +
      _r22 +
      _r21 +
      _r20 +
      _r19 +
      _r18 +
      _r17 +
      _r16 +
      _r15 +
      _r14 +
      _r13 +
      _r12 +
      _r11 +
      _r10 +
      _r9 +
      _r8 +
      _r7 +
      _r6 +
      _r5 +
      _r4 +
      _r3 +
      _r2 +
      _r1
    );
  }

  proc mstore(idx : uint256, val : uint256): unit = {
    var  _w248,  _w240,  _w232,  _w224,  _w216,  _w208,  _w200,  _w192,  _w184,  _w176,  _w168,  _w160,  _w152,  _w144,  _w136,  _w128,  _w120,  _w112,  _w104,  _w96,  _w88,  _w80,  _w72,  _w64,  _w56,  _w48,  _w40,  _w32,  _w24,  _w16,  _w8,  _w0;
     _w248 <- splitMask (W256.masklsb 248) val;
     _w240 <- splitMask (W256.masklsb 240) ( _w248.`1);
     _w232 <- splitMask (W256.masklsb 232) ( _w240.`1);
     _w224 <- splitMask (W256.masklsb 224) ( _w232.`1);
     _w216 <- splitMask (W256.masklsb 216) ( _w224.`1);
     _w208 <- splitMask (W256.masklsb 208) ( _w216.`1);
     _w200 <- splitMask (W256.masklsb 200) ( _w208.`1);
     _w192 <- splitMask (W256.masklsb 192) ( _w200.`1);
     _w184 <- splitMask (W256.masklsb 184) ( _w192.`1);
     _w176 <- splitMask (W256.masklsb 176) ( _w184.`1);
     _w168 <- splitMask (W256.masklsb 168) ( _w176.`1);
     _w160 <- splitMask (W256.masklsb 160) ( _w168.`1);
     _w152 <- splitMask (W256.masklsb 152) ( _w160.`1);
     _w144 <- splitMask (W256.masklsb 144) ( _w152.`1);
     _w136 <- splitMask (W256.masklsb 136) ( _w144.`1);
     _w128 <- splitMask (W256.masklsb 128) ( _w136.`1);
     _w120 <- splitMask (W256.masklsb 120) ( _w128.`1);
     _w112 <- splitMask (W256.masklsb 112) ( _w120.`1);
     _w104 <- splitMask (W256.masklsb 104) ( _w112.`1);
     _w96 <- splitMask (W256.masklsb 96) ( _w104.`1);
     _w88 <- splitMask (W256.masklsb 88) ( _w96.`1);
     _w80 <- splitMask (W256.masklsb 80) ( _w88.`1);
     _w72 <- splitMask (W256.masklsb 72) ( _w80.`1);
     _w64 <- splitMask (W256.masklsb 64) ( _w72.`1);
     _w56 <- splitMask (W256.masklsb 56) ( _w64.`1);
     _w48 <- splitMask (W256.masklsb 48) ( _w56.`1);
     _w40 <- splitMask (W256.masklsb 40) ( _w48.`1);
     _w32 <- splitMask (W256.masklsb 32) ( _w40.`1);
     _w24 <- splitMask (W256.masklsb 24) ( _w32.`1);
     _w16 <- splitMask (W256.masklsb 16) ( _w24.`1);
     _w8 <- splitMask (W256.masklsb 8) ( _w16.`1);
     _w0 <- splitMask (W256.masklsb 0) ( _w8.`1);

    memory <- memory.[idx<- _w248.`2 `>>>` 248];
    memory <- memory.[(idx+W256.of_int 1)<-_w240.`2 `>>>` 240];
    memory <- memory.[(idx+W256.of_int 2)<-_w232.`2 `>>>` 232];
    memory <- memory.[(idx+W256.of_int 3)<-_w224.`2 `>>>` 224];
    memory <- memory.[(idx+W256.of_int 4)<-_w216.`2 `>>>` 216];
    memory <- memory.[(idx+W256.of_int 5)<-_w208.`2 `>>>` 208];
    memory <- memory.[(idx+W256.of_int 6)<-_w200.`2 `>>>` 200];
    memory <- memory.[(idx+W256.of_int 7)<-_w192.`2 `>>>` 192];
    memory <- memory.[(idx+W256.of_int 8)<-_w184.`2 `>>>` 184];
    memory <- memory.[(idx+W256.of_int 9)<-_w176.`2 `>>>` 176];
    memory <- memory.[(idx+W256.of_int 10)<-_w168.`2 `>>>` 168];
    memory <- memory.[(idx+W256.of_int 11)<-_w160.`2 `>>>` 160];
    memory <- memory.[(idx+W256.of_int 12)<-_w152.`2 `>>>` 152];
    memory <- memory.[(idx+W256.of_int 13)<-_w144.`2 `>>>` 144];
    memory <- memory.[(idx+W256.of_int 14)<-_w136.`2 `>>>` 136];
    memory <- memory.[(idx+W256.of_int 15)<-_w128.`2 `>>>` 128];
    memory <- memory.[(idx+W256.of_int 16)<-_w120.`2 `>>>` 120];
    memory <- memory.[(idx+W256.of_int 17)<-_w112.`2 `>>>` 112];
    memory <- memory.[(idx+W256.of_int 18)<-_w104.`2 `>>>` 104];
    memory <- memory.[(idx+W256.of_int 19)<-_w96.`2 `>>>` 96];
    memory <- memory.[(idx+W256.of_int 20)<-_w88.`2 `>>>` 88];
    memory <- memory.[(idx+W256.of_int 21)<-_w80.`2 `>>>` 80];
    memory <- memory.[(idx+W256.of_int 22)<-_w72.`2 `>>>` 72];
    memory <- memory.[(idx+W256.of_int 23)<-_w64.`2 `>>>` 64];
    memory <- memory.[(idx+W256.of_int 24)<-_w56.`2 `>>>` 56];
    memory <- memory.[(idx+W256.of_int 25)<-_w48.`2 `>>>` 48];
    memory <- memory.[(idx+W256.of_int 26)<-_w40.`2 `>>>` 40];
    memory <- memory.[(idx+W256.of_int 27)<-_w32.`2 `>>>` 32];
    memory <- memory.[(idx+W256.of_int 28)<-_w24.`2 `>>>` 24];
    memory <- memory.[(idx+W256.of_int 29)<-_w16.`2 `>>>` 16];
    memory <- memory.[(idx+W256.of_int 30)<-_w8.`2 `>>>` 8];
    memory <- memory.[(idx+W256.of_int 31)<-_w0.`2 `>>>` 0];
  }

  proc mstore8(idx : uint256, val : uint256) : unit = {
    memory <- memory.[idx<-(val `&` W256.masklsb 8)];
  }

  proc evm_return(retOff : uint256, retSize : uint256) : unit = {
    (* TODO: Implement return *)
    return ();
  }

  proc gas() : uint256 = {
    (* Confirm ok *)
    return W256.of_int 42;
  }

  proc keccak256(off : uint256, size : uint256) : uint256 = {
    (* TODO: relate to keccak_f *)
    return W256.zero;
  }

  proc staticcall(gas : uint256, addr : uint256, argOff : uint256, argSize : uint256, retOff : uint256, retSize : uint256) : uint256 = {
    var succ;
    if (addr = W256.of_int 5) {
      (* TODO: modexp *)
      succ <- W256.zero;
    } else {
      if (addr = W256.of_int 6) {
        (* TODO: ecAdd *)
        succ <- W256.zero;
      } else {
        if (addr = W256.of_int 7) {
          (* TODO: ecMul *)
          succ <- W256.zero;
        } else {
          if (addr = W256.of_int 8) {
            (* TODO: ecPairing *)
            succ <- W256.zero;
          } else {
              succ <- W256.zero;
          }
        }
      }
    }
    return succ;
  }

  proc revert(x : uint256, y : uint256) : unit = {
    reverted <- true;
  }

  proc calldataload(i : uint256) : uint256 = {
    return calldata.[W256.to_uint i];
  }
}.

theory ConcretePrimops.

op mload (memory: mem) (idx: uint256) =
    memory.[idx+ W256.of_int 31] +
    (memory.[idx+ W256.of_int 30] `<<<` 8) +
    (memory.[idx+ W256.of_int 29] `<<<` 16) +
    (memory.[idx+ W256.of_int 28] `<<<` 24) +
    (memory.[idx+ W256.of_int 27] `<<<` 32) +
    (memory.[idx+ W256.of_int 26] `<<<` 40) +
    (memory.[idx+ W256.of_int 25] `<<<` 48) +
    (memory.[idx+ W256.of_int 24] `<<<` 56) +
    (memory.[idx+ W256.of_int 23] `<<<` 64) +
    (memory.[idx+ W256.of_int 22] `<<<` 72) +
    (memory.[idx+ W256.of_int 21] `<<<` 80) +
    (memory.[idx+ W256.of_int 20] `<<<` 88) +
    (memory.[idx+ W256.of_int 19] `<<<` 96) +
    (memory.[idx+ W256.of_int 18] `<<<` 104) +
    (memory.[idx+ W256.of_int 17] `<<<` 112) +
    (memory.[idx+ W256.of_int 16] `<<<` 120) +
    (memory.[idx+ W256.of_int 15] `<<<` 128) +
    (memory.[idx+ W256.of_int 14] `<<<` 136) +
    (memory.[idx+ W256.of_int 13] `<<<` 144) +
    (memory.[idx+ W256.of_int 12] `<<<` 152) +
    (memory.[idx+ W256.of_int 11] `<<<` 160) +
    (memory.[idx+ W256.of_int 10] `<<<` 168) +
    (memory.[idx+ W256.of_int 9] `<<<` 176) +
    (memory.[idx+ W256.of_int 8] `<<<` 184) +
    (memory.[idx+ W256.of_int 7] `<<<` 192) +
    (memory.[idx+ W256.of_int 6] `<<<` 200) +
    (memory.[idx+ W256.of_int 5] `<<<` 208) +
    (memory.[idx+ W256.of_int 4] `<<<` 216) +
    (memory.[idx+ W256.of_int 3] `<<<` 224) +
    (memory.[idx+ W256.of_int 2] `<<<` 232) +
    (memory.[idx+ W256.of_int 1] `<<<` 240) +
    (memory.[idx] `<<<` 248)
axiomatized by mLoadE.

lemma mload_spec (memory: mem) (idx: uint256):
hoare [ Primops.mload :
    arg = idx /\
    Primops.memory = memory ==>
      res = mload memory idx /\
      Primops.memory = memory
    ].
    proof.
      progress.
      proc.
      wp.
      skip.
      progress.
      rewrite /mload.
      reflexivity.
  qed.

op apply_mstore (memory: mem) (idx val: uint256): mem.
op uint256_frame (memory_pre memory_post: mem) (idx: uint256) = forall (idx2: uint256), W256.of_int 31 < idx2 - idx => memory_post.[idx2] = memory_pre.[idx2].
axiom apply_mstore_def (memory_pre memory_post: mem) (idx val: uint256):
memory_post = apply_mstore memory_pre idx val <=> (
  mload memory_post idx = val /\
  uint256_frame memory_pre memory_post idx
).
lemma apply_mstore_mload_same (memory: mem) (idx val: uint256):
    mload (apply_mstore memory idx val) idx = val.
    proof.
      smt.
  qed.

lemma apply_mstore_mload_diff (memory: mem) (idx idx2 val: uint256):
    W256.of_int 31 < idx2 - idx => W256.of_int 31 < idx - idx2 =>  mload (apply_mstore memory idx val) idx2 = mload memory idx2.
proof.
  progress.
  rewrite /mload.
  pose memory_post := apply_mstore memory idx val.
  have h_full: mload memory_post idx = val /\ uint256_frame memory memory_post idx. by smt.
  have h_frame: uint256_frame memory memory_post idx. smt.
  rewrite /uint256_frame in h_frame.
  have h31: forall (offset: int), 0 <= offset => offset < 32 => memory_post.[idx2 + W256.of_int offset] = memory.[idx2 + W256.of_int offset].
  progress.
  apply h_frame.
  rewrite /W256.\ult.
  by smt.
  have h0: memory_post.[idx2] = memory.[idx2].
  by smt.
  (rewrite (h31 31); first trivial); first trivial.
  (rewrite (h31 30); first trivial); first trivial.
  (rewrite (h31 29); first trivial); first trivial.
  (rewrite (h31 28); first trivial); first trivial.
  (rewrite (h31 27); first trivial); first trivial.
  (rewrite (h31 26); first trivial); first trivial.
  (rewrite (h31 25); first trivial); first trivial.
  (rewrite (h31 24); first trivial); first trivial.
  (rewrite (h31 23); first trivial); first trivial.
  (rewrite (h31 22); first trivial); first trivial.
  (rewrite (h31 21); first trivial); first trivial.
  (rewrite (h31 20); first trivial); first trivial.
  (rewrite (h31 19); first trivial); first trivial.
  (rewrite (h31 18); first trivial); first trivial.
  (rewrite (h31 17); first trivial); first trivial.
  (rewrite (h31 16); first trivial); first trivial.
  (rewrite (h31 15); first trivial); first trivial.
  (rewrite (h31 14); first trivial); first trivial.
  (rewrite (h31 13); first trivial); first trivial.
  (rewrite (h31 12); first trivial); first trivial.
  (rewrite (h31 11); first trivial); first trivial.
  (rewrite (h31 10); first trivial); first trivial.
  (rewrite (h31 9); first trivial); first trivial.
  (rewrite (h31 8); first trivial); first trivial.
  (rewrite (h31 7); first trivial); first trivial.
  (rewrite (h31 6); first trivial); first trivial.
  (rewrite (h31 5); first trivial); first trivial.
  (rewrite (h31 4); first trivial); first trivial.
  (rewrite (h31 3); first trivial); first trivial.
  (rewrite (h31 2); first trivial); first trivial.
  (rewrite (h31 1); first trivial); first trivial.
    rewrite h0.
    reflexivity.
qed.

lemma neq_of_lt (idx idx2: uint256):
    W256.of_int 31 < idx2 - idx => idx2 <> idx.
    proof.
      progress.
      smt.
    qed.
    
lemma add_neq_of_lt (idx idx2: uint256) (offset: int):
    W256.of_int 31 < idx2 - idx =>  0 < offset /\ offset < 32 => idx2 <> (idx + W256.of_int offset).
    proof.
      progress.
      smt.
    qed.
    
lemma mstore_spec:
    forall (memory: mem) (idx': uint256) (val': uint256),
hoare [ Primops.mstore :
    arg = (idx', val') /\
    Primops.memory = memory ==>
      (*(forall (idx2: uint256), (idx2 < idx' \/ idx' + W256.of_int 31 < idx2) => Primops.memory.[idx2] = memory.[idx2]) /\ -- TODO frame rule*)
    (* mload Primops.memory idx' = val' *)
      Primops.memory = apply_mstore memory idx' val'
    ].
    proof.
      progress.
      proc.
      wp.
      skip.
    move => &hr h_args.
      have h_idx: idx{hr} = idx'.
      smt.
      have h_val: val{hr} = val'.
      smt.
      have h_mem: Primops.memory{hr} = memory.
      smt.
    move => x248 x240 x232 x224 x216 x208 x200 x192 x184 x176 x168 x160 x152 x144 x136 x128 x120 x112 x104 x96 x88 x80 x72 x64 x56 x48 x40 x32 x24 x16 x8.
      rewrite apply_mstore_def.
    split.
      rewrite h_mem.
      rewrite /mload.
      rewrite h_idx.
      rewrite {1} Map.get_set_sameE.
      rewrite {1} get_set_offsets_neq; first trivial.
      rewrite {1} Map.get_set_sameE.
      rewrite masklsb_zero.
      rewrite splitMask_zero.
      rewrite shr_zero.
      rewrite /x8.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 2! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x16.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 3! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x24.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.    
      do 4! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x32.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.    
      do 5! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x40.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.    
      do 6! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x48.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 7! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x56.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 8! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x64.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 9! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x72.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 10! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x80.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 11! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x88.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 12! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x96.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 13! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x104.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 14! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x112.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 15! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x120.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 16! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x128.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 17! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x136.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 18! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x144.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 19! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x152.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 20! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x160.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 21! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x168.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 22! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x176.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 23! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x184.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 24! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x192.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 25! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x200.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 26! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x208.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 27! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x216.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 28! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x224.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 29! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x232.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 30! (rewrite {1} get_set_offsets_neq; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x240.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      do 31! (rewrite {1} get_set_offset; first trivial).
      rewrite {1} Map.get_set_sameE.
      rewrite /x248.
      rewrite splitMask2_shr_shl; first trivial.
      rewrite splitMask_add.
      exact h_val.
      rewrite /uint256_frame.
    move => idx2 h_idx2.
      rewrite h_idx.
      do 31! ((rewrite {1} Map.get_set_neqE; first (apply add_neq_of_lt; first apply h_idx2)); first trivial).
      rewrite Map.get_set_neqE; first apply neq_of_lt.
      exact h_idx2.
      rewrite h_mem.
      reflexivity.
qed.
    

end ConcretePrimops.
