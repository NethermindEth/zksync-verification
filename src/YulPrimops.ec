pragma Goals:printall.

require import Logic Array.
require export UInt256 Memory.

op calldata : uint256 array.
(* op keccak256 : uint256 array -> uint256. *)

module Primops = {
  var memory : mem
  var reverted : bool

  proc mload(idx : uint256) : uint256 = {
    (* _1 is the most significant byte *)
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

  proc ret(retOff : uint256, retSize : uint256) : unit = {
    (* TODO: Implement return *)
    return ();
  }

  proc gas() : uint256 = {
    (* Confirm ok *)
    return W256.of_int 42;
  }

  proc iszero(v : uint256) : uint256 = {
    var ref;
    if (v = W256.of_int 0) {
      ref <- W256.one;
    } else {
      ref <- W256.zero;
    }
    return ref;
  }

  proc mulmod(a : uint256, b : uint256, n : uint256) : uint256 = {
    return (a * b) %% n;
  }

  proc addmod(a : uint256, b : uint256, n : uint256) : uint256 = {
    return (a + b) %% n;
  }

  proc keccak256(v : uint256) : uint256 = {
    (* TODO: return sample from uniform distribution over uint256 *)
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

  proc revert() : unit = {
    reverted <- true;
  }

  proc calldataload(i : uint256) : uint256 = {
    return calldata.[W256.to_uint i];
  }
}.
