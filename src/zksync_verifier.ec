pragma Goals:printall.
require import Int Logic IntDiv CoreMap SmtMap Array.

type uint256 = int.
type mem = (uint256, uint256) map.

op p = 21888242871839275222246405745257275088696311157297823662689037894645226208583.
op calldata : uint256 array.

module Test = {

  proc mload(a : uint256, m : mem) : uint256 = {
    return m.[a];
  }

  proc mstore(a : uint256, v : uint256, m : mem) : mem = {
    return m.[a<-v];
  }

  proc mstore8(a : uint256, v : uint256, m : mem) : mem = {
    (* TODO: memory model? *)
    return m;
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
  
  proc calldatasize(i : uint256) : uint256 = {
    return size(calldata);
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
  
  proc pointNegate(m : mem, point : uint256) : mem = {
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
    forall (m : mem) (point_addr : uint256),
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
            


(* Some potentially useful lemmas to prove mid-level specs *)
            
lemma mod_m_lt_m :
    forall (a m : int), 0 < m => a %% m < m.
    smt.
    qed.

lemma mod_eq_self : forall (a m : int), 0 < m => 0 <= a => a < m => a %% m = a.
    smt.
    qed.
    
lemma mod_mod_eq_mod :
    forall (m1 m2 v : int), 0 < m1 => m1 <= m2 => (v %% m1) %% m2 = v %% m1.
    progress.
    smt.
    qed.
