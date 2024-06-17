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
    var _1, _2; (*, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21, _22, _23, _24, _25, _26, _27, _28, _29, _30, _31, _32; *)


    _1 <- memory.[idx] `<<<` 128;
    _2 <- memory.[idx+ W256.of_int 1] `<<<` 0;

    


    (* _3 <- memory.[idx+ W256.of_int 2] `<<<` 232;
    _4 <- memory.[idx+ W256.of_int 3] `<<<` 224;
    _5 <- memory.[idx+ W256.of_int 4] `<<<` 216;
    _6 <- memory.[idx+ W256.of_int 5] `<<<` 208;
    _7 <- memory.[idx+ W256.of_int 6] `<<<` 200;
    _8 <- memory.[idx+ W256.of_int 7] `<<<` 192;
    _9 <- memory.[idx+ W256.of_int 8] `<<<` 184;
    _10 <- memory.[idx+ W256.of_int 9] `<<<` 176;
    _11 <- memory.[idx+ W256.of_int 10] `<<<` 168;
    _12 <- memory.[idx+ W256.of_int 11] `<<<` 160;
    _13 <- memory.[idx+ W256.of_int 12] `<<<` 152;
    _14 <- memory.[idx+ W256.of_int 13] `<<<` 144;
    _15 <- memory.[idx+ W256.of_int 14] `<<<` 136;
    _16 <- memory.[idx+ W256.of_int 15] `<<<` 128;
    _17 <- memory.[idx+ W256.of_int 16] `<<<` 120;
    _18 <- memory.[idx+ W256.of_int 17] `<<<` 112;
    _19 <- memory.[idx+ W256.of_int 18] `<<<` 104;
    _20 <- memory.[idx+ W256.of_int 19] `<<<` 96;
    _21 <- memory.[idx+ W256.of_int 20] `<<<` 88;
    _22 <- memory.[idx+ W256.of_int 21] `<<<` 80;
    _23 <- memory.[idx+ W256.of_int 22] `<<<` 72;
    _24 <- memory.[idx+ W256.of_int 23] `<<<` 64;
    _25 <- memory.[idx+ W256.of_int 24] `<<<` 56;
    _26 <- memory.[idx+ W256.of_int 25] `<<<` 48;
    _27 <- memory.[idx+ W256.of_int 26] `<<<` 40;
    _28 <- memory.[idx+ W256.of_int 27] `<<<` 32;
    _29 <- memory.[idx+ W256.of_int 28] `<<<` 24;
    _30 <- memory.[idx+ W256.of_int 29] `<<<` 16;
    _31 <- memory.[idx+ W256.of_int 30] `<<<` 8;
    _32 <- memory.[idx+ W256.of_int 31]; *)
    return (
      _1 +
      _2 (* +
      _3 +
      _4 +
      _5 +
      _6 +
      _7 +
      _8 +
      _9 +
      _10 +
      _11 +
      _12 +
      _13 +
      _14 +
      _15 +
      _16 +
      _17 +
      _18 +
      _19 +
      _20 +
      _21 +
      _22 +
      _23 +
      _24 +
      _25 +
      _26 +
      _27 +
      _28 +
      _29 +
      _30 +
      _31 +
      _32 *)
    );
  }

  proc mstore(idx : uint256, val : uint256): unit = {
    var _1, _2;
    (* memory <- memory.[(idx + W256.of_int 31)<-(val `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 30)<-((val `>>>` 8) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 29)<-((val `>>>` 16) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 28)<-((val `>>>` 24) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 27)<-((val `>>>` 32) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 26)<-((val `>>>` 40) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 25)<-((val `>>>` 48) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 24)<-((val `>>>` 56) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 23)<-((val `>>>` 64) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 22)<-((val `>>>` 72) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 21)<-((val `>>>` 80) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 20)<-((val `>>>` 88) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 19)<-((val `>>>` 96) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 18)<-((val `>>>` 104) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 17)<-((val `>>>` 112) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 16)<-((val `>>>` 120) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 15)<-((val `>>>` 128) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 14)<-((val `>>>` 136) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 13)<-((val `>>>` 144) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 12)<-((val `>>>` 152) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 11)<-((val `>>>` 160) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 10)<-((val `>>>` 168) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 9)<-((val `>>>` 176) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 8)<-((val `>>>` 184) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 7)<-((val `>>>` 192) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 6)<-((val `>>>` 200) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 5)<-((val `>>>` 208) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 4)<-((val `>>>` 216) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 3)<-((val `>>>` 224) `&` W256.masklsb 8)];
    memory <- memory.[(idx + W256.of_int 2)<-((val `>>>` 232) `&` W256.masklsb 8)]; *)

    (* memory <- memory.[(idx + W256.of_int 1)<-((val `>>>` 0) `&` W256.masklsb 128)];
    memory <- memory.[idx<-((val `>>>` 128) `&` W256.masklsb 128)]; *)

    _1 <- (splitMask (W256.masklsb 128) val).`2 `>>>` 128;
    _2 <- (splitMask (W256.masklsb 128) val).`1;

    memory <- memory.[idx<-_1];
    memory <- memory.[(idx+W256.of_int 1)<-_2];
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
