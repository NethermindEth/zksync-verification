pragma Goals:printall.

require import AllCore Int IntDiv.
require import Array.
require import Logic.
require import PurePrimops.
require import Utils.
require export UInt256 Memory EllipticCurve.

module Primops = {
  var memory : mem
  var ret_data : uint256 array
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
      var i : uint256;
      i <- W256.zero;
      ret_data <- Array.mkarray (List.nseq (W256.to_uint retSize) W256.zero);
      while (i < retSize) {
      ret_data.[W256.to_uint i] <- memory.[retOff + i];
      i <- i + W256.one;
      }
      return ();
  }

  proc gas() : uint256 = {
    (* Confirm ok *)
    return W256.of_int 42;
  }

  proc keccak256(off : uint256, size : uint256) : uint256 = {
      (* TODO: relate to keccak_f *)
      var input : uint256 array;
      var i : uint256;
      i <- W256.zero;
      input <- Array.mkarray (List.nseq (W256.to_uint size) W256.zero);
      while (i < size) {
      input.[W256.to_uint i] <- memory.[off + i];
      i <- i + W256.one;
      }
    
      return PurePrimops.keccak256_f input;
  }

  proc staticcall(gas : uint256, addr : uint256, argOff : uint256, argSize : uint256, retOff : uint256, retSize : uint256) : uint256 = {
      var succ;
      var bsize, esize, msize : uint256;
      var base, exp, mod;
      var x1, y1, x2, y2;
      var s;
      var s_F;
      var x1_F, y1_F, x2_F, y2_F;
      var result;
      var result_unwrap;
      if (addr = W256.of_int 5) {
        bsize <@ mload(argOff);
        esize <@ mload(argOff + W256.of_int 32);
        msize <@ mload(argOff + W256.of_int 64);
        if (bsize = (W256.of_int 32) /\ esize = (W256.of_int 32) /\ msize = (W256.of_int 32) /\ retSize = (W256.of_int 32) /\ argSize = (W256.of_int 192)) {
          base <@ mload(argOff + W256.of_int 96);
          exp  <@ mload(argOff + W256.of_int 128);
          mod  <@ mload(argOff + W256.of_int 160);
          mstore(retOff, W256.of_int (((W256.to_uint base) ^ (W256.to_uint exp)) %% (W256.to_uint mod)));
          succ <- W256.one;
        } else {
          succ <- W256.zero;
        }
      } else {
        if (addr = W256.of_int 6) {
          x1 <@ mload(argOff);
          y1 <@ mload(argOff + W256.of_int 32);
          x2 <@ mload(argOff + W256.of_int 64);
          y2 <@ mload(argOff + W256.of_int 96);
          x1_F <- ZModField.inzmod (W256.to_sint x1);
          y1_F <- ZModField.inzmod (W256.to_sint y1);
          x2_F <- ZModField.inzmod (W256.to_sint x2);
          y2_F <- ZModField.inzmod (W256.to_sint y2);
          if (x1 <> x1 %% W256.of_int p \/ y1 <> y1 %% W256.of_int p \/ x2 <> x2 %% W256.of_int p \/ y2 <> y2 %% W256.of_int p) {
            succ <- W256.zero;
          } else {
              if (!(on_curve (x1_F, y1_F)) \/ !(on_curve ((x2_F, y2_F)))) {
                 succ <- W256.zero;
            } else {
                result <- ecAdd_precompile x1_F y1_F x2_F y2_F;
                if (is_none result) {
                  succ <- W256.zero;
                } else {
                    result_unwrap <- odflt (ZModField.zero, ZModField.zero) result;
                    mstore(retOff, W256.of_int (ZModField.asint (fst result_unwrap)));
                    mstore(retOff + W256.of_int 32, W256.of_int (ZModField.asint (snd (result_unwrap))));
                    succ <- W256.one;
                }                
            }
          }
        } else {
          if (addr = W256.of_int 7) {
            x1 <@ mload(argOff);
            y1 <@ mload(argOff + W256.of_int 32);
            s <@ mload(argOff + W256.of_int 64);
            x1_F <- ZModField.inzmod (W256.to_sint x1);
            y1_F <- ZModField.inzmod (W256.to_sint y1);
            s_F <- ZModField.inzmod (W256.to_sint s);
            if (x1 <> x1 %% W256.of_int p \/ y1 <> y1 %% W256.of_int p) {
              succ <- W256.zero;
            } else {
                if (!(on_curve (x1_F, y1_F))) {
                  succ <- W256.zero;
              } else {
                  result <- ecMul_precompile x1_F y1_F s_F;
                  if (is_none result) {
                    succ <- W256.zero;
                  } else {
                      result_unwrap <- odflt (ZModField.zero, ZModField.zero) result;
                      mstore(retOff, W256.of_int (ZModField.asint (fst result_unwrap)));
                      mstore(retOff + W256.of_int 32, W256.of_int (ZModField.asint (snd (result_unwrap))));
                      succ <- W256.one;
                  }                
              }
            }
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
    return PurePrimops.calldata.[W256.to_uint i];
  }
}.

theory ConcretePrimops.

lemma mload_pspec (memory: mem) (idx: uint256):
phoare [ Primops.mload :
    arg = idx /\
    Primops.memory = memory ==>
      res = PurePrimops.mload memory idx /\
      Primops.memory = memory
    ] = 1%r.
    proof.
      progress.
      proc.
      wp.
      skip.
      progress.
      rewrite /mload.
      reflexivity.
  qed.

lemma mload_spec (memory: mem) (idx: uint256):
hoare [ Primops.mload :
    arg = idx /\
    Primops.memory = memory ==>
      res = PurePrimops.mload memory idx /\
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
    
lemma mstore_pspec:
    forall (memory: mem) (idx': uint256) (val': uint256),
phoare [ Primops.mstore :
    arg = (idx', val') /\
    Primops.memory = memory /\
    mem_wellformed memory ==>
      Primops.memory = PurePrimops.mstore memory idx' val'
    ] = 1%r.
    proof.
      progress.
      proc.
      wp.
      skip.
    move => &hr h_args.
      have h_idx: idx{hr} = idx'.
      smt.
      have h_val: val{hr} = val'.
      admit. (* TODO add sufficient weakening lemmas to utils *)
      have h_mem: Primops.memory{hr} = memory.
      smt.
    move => x248 x240 x232 x224 x216 x208 x200 x192 x184 x176 x168 x160 x152 x144 x136 x128 x120 x112 x104 x96 x88 x80 x72 x64 x56 x48 x40 x32 x24 x16 x8.
      apply PurePrimops.mstore_of_load_and_frame.
      smt ().
      do 32! (rewrite write_byte_maintains_wellformed; first admit). (* mem wellformedness *)
      smt ().
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
      do 31! (rewrite {1} Map.get_set_neqE; first by smt (PurePrimops.add_neq_of_lt)).
      rewrite Map.get_set_neqE.
      apply neq_of_lt.
      exact h_idx2.
      rewrite h_mem.
      reflexivity.
  qed.

lemma mstore_spec:
    forall (memory: mem) (idx': uint256) (val': uint256),
hoare [ Primops.mstore :
    arg = (idx', val') /\
    Primops.memory = memory /\
    mem_wellformed memory ==>
      Primops.memory = PurePrimops.mstore memory idx' val'
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
      admit. (* TODO add sufficient weakening lemmas to utils *)
      have h_mem: Primops.memory{hr} = memory.
      smt.
    move => x248 x240 x232 x224 x216 x208 x200 x192 x184 x176 x168 x160 x152 x144 x136 x128 x120 x112 x104 x96 x88 x80 x72 x64 x56 x48 x40 x32 x24 x16 x8.
      apply PurePrimops.mstore_of_load_and_frame.
      smt ().
      do 32! (rewrite write_byte_maintains_wellformed; first admit). (* mem wellformedness *)
      smt ().
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
      do 31! (rewrite {1} Map.get_set_neqE; first by smt (PurePrimops.add_neq_of_lt)).
      rewrite Map.get_set_neqE.
      apply neq_of_lt.
      exact h_idx2.
      rewrite h_mem.
      reflexivity.
    qed.

end ConcretePrimops.
