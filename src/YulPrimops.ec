pragma Goals:printall.

require import Logic Array.
require export UInt256 Memory.

op calldata : uint256 array.

module Primops = {
  var m : mem

  proc mload(a : uint256) : uint256 = { 
    return m.[a];
  }

  proc mstore(a : uint256, v : uint256): unit = {
    m <- m.[a<-v];
  }

  proc mstore8(a : uint256, v : uint256) : uint256 = {
    (* TODO: memory model? *)
    return m.[a];
  }

  proc ret(retOff : uint256, retSize : uint256) : unit = {
    (* TODO: Implement return, needs to be differentiable from revert *)
    return ();
  }
  
  proc gas() : uint256 = {
    (* Confirm ok *)
    return 42;
  }
  
  proc iszero(v : uint256) : uint256 = {
    var ref;
    if (v = 0) {
      ref <- 1;
    } else {
      ref <- 0;
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
    return 0;
  }

  proc staticcall(gas : uint256, addr : uint256, argOff : uint256, argSize : uint256, retOff : uint256, retSize : uint256, m : mem) : uint256 * mem = {
    var succ, m';
    if (addr = 5) {
      (* TODO: modexp *)
      succ <- 0;
      m' <- m;
    } else {
      if (addr = 6) {
        (* TODO: ecAdd *)
        succ <- 0;
        m' <- m;
      } else {
        if (addr = 7) {
          (* TODO: ecMul *)
          succ <- 0;
          m' <- m;
        } else {
          if (addr = 8) {
            (* TODO: ecPairing *)
            succ <- 0;
            m' <- m;
          } else {
              succ <- 0;
              m' <- m;
          }
        }
      }
    }
    return (succ, m');
  }  

  proc revert() : unit = {
    (* TODO: Implement revert, needs to be differentiable from return *)
    return ();
  }

  proc calldataload(i : uint256) : uint256 = {
    return calldata.[i];
  }
}.
