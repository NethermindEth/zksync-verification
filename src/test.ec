pragma Goals:printall.
require import Int Logic IntDiv CoreMap SmtMap Array.

type uint256 = int.
type MemoryMap = (uint256, uint256) map.

op p = 21888242871839275222246405745257275088696311157297823662689037894645226208583.
op calldata : uint256 array.

module Test = {

  proc mload(a : uint256, m : MemoryMap) : uint256 = {
    return m.[a];
  }

  proc mstore(a : uint256, v : uint256, m : MemoryMap) : MemoryMap = {
    return m.[a<-v];
  }

  proc mstore8(a : uint256, v : uint256, m : MemoryMap) : MemoryMap = {
    (* TODO *)
    return m;
  }

  proc revert() : unit = {
    (* TODO *)
    return ();
  }

  (* proc staticcall()  *)

  proc calldatasize(i : uint256) : uint256 = {
    return size(calldata);
  }
  
  proc calldataload(i : uint256) : uint256 = {
    return calldata.[i];
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

  proc gas() : uint256 = {
    return 42;
  }
  
  proc pointNegate(m : MemoryMap, point : uint256) : MemoryMap = {
      var _1, _2, _3, pY, tmp166, tmp167, tmp168, _6, _7, tmp170;
      _1 <- 32;
      _2 <- point + _1;
      tmp166 <@ mload(_2, m);
      pY <- tmp166;
      tmp167 <- pY;
      if (tmp167 = 0)
      {
        tmp168 <@ mload(point, m);
        _3 <- tmp168;
        if (_3 = 0)
        {
        }
        tmp170 <- m;
      } else {
          _6 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
          _7 <- _6 - pY;
          tmp170 <@ mstore(_2, _7, m);
      }
      return tmp170;
    }
  
}.
    
lemma pointNegate_lemma :
    forall (m : MemoryMap) (point_addr : uint256),
    (m.[point_addr] <> 0 \/ m.[point_addr + 32] <> 0) /\ m.[point_addr + 32] < p /\ 0 < m.[point_addr + 32] =>
        hoare [ Test.pointNegate : arg = (m, point_addr) ==>
          (m.[point_addr] = res.[point_addr] /\ res.[point_addr + 32] = (-m.[point_addr + 32]) %% p)]. 
            progress.
            proc.
            simplify.
            inline Test.mload.
            inline Test.mstore.
            wp.
            skip.
            progress.
            smt.
            smt.
            rewrite -/p.
            smt.
            qed.            
            

            
