pragma Goals:printall.

require import Logic Array.
require export UInt256 Memory.

op calldata : uint256 array.
(* op keccak256 : uint256 array -> uint256. *)

module Primops = {
  var memory : mem
  var reverted : bool

  proc mload(a : uint256) : uint256 = {
    return memory.[a];
  }

  proc mstore(a : uint256, v : uint256): unit = {
    memory <- memory.[a<-v];
  }

  proc mstore8(a : uint256, v : uint256) : unit = {
    (* TODO: memory model? *)
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
