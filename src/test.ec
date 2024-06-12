pragma Goals:printall.
require import Int Logic IntDiv CoreMap SmtMap.

type MemoryMap = (int, int) map.



op p = 21888242871839275222246405745257275088696311157297823662689037894645226208583.

(*
op "_.[_<-_]" ['a, 'b] (f : 'a -> 'b) (x : 'a) (y : 'b) =
  fun x' => if x = x' then y else f x'.

lemma fupdateE ['a 'b] (f : 'a -> 'b) (x x' : 'a) (y : 'b) :
  f.[x <- y] x' = if x = x' then y else f x'.
proof. by []. qed.

lemma fupdate_eq ['a 'b] (f : 'a -> 'b) (x : 'a) (y : 'b) :
  f.[x <- y] x = y.
proof. by []. qed.

lemma fupdate_neq ['a 'b] (f : 'a -> 'b) (x x' : 'a) (y : 'b) :
  x <> x' => f.[x <- y] x' = f x'.
proof. by move=> @/"_.[_<-_]" ->. qed.
*)
module Test = {

  proc mload(m : MemoryMap, a : int) : int = {
    return m.[a];
  }

  proc mstore(m : MemoryMap, a : int, v : int) : MemoryMap = {
    return m.[a<-v];
  }
  
  proc pointNegate(m : MemoryMap, point : int): MemoryMap = {
      var _1, _2, _3, pY, tmp166, tmp167, tmp168, _6, _7, tmp170;
      _1 <- 32;
      _2 <- point + _1;
      tmp166 <@ mload(m, _2);
      pY <- tmp166;
      tmp167 <- pY;
      if (tmp167 = 0)
      {
        tmp168 <@ mload(m, point);
        _3 <- tmp168;
        if (_3 = 0)
        {
        }
        tmp170 <- m;
      } else {
          _6 <- 21888242871839275222246405745257275088696311157297823662689037894645226208583;
          _7 <- _6 - pY;
          tmp170 <@ mstore(m, _2, _7);
      }
      return tmp170;
  }

  proc stupid(a : int, b : int) : int = {
    return a + b;
  }
  
}.

lemma stupid_lemma :
    forall (a b : int), hoare[ Test.stupid : arg = (a,b) ==> res = a + b].
    progress.
    proc.
    skip.
    progress.
    qed.

print ( < ).
    
lemma pointNegate_lemma :
    forall (m : MemoryMap) (point_addr : int),
    m.[point_addr] <> 0 \/ m.[point_addr + 32] <> 0 => m.[point_addr + 32] < p
    => 0 < m.[point_addr + 32] =>
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
            
        
        
        
        
        
