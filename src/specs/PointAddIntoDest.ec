pragma Goals:printall.

require import Array.
require import EllipticCurve.
require import Logic.
require import Memory.
require import PurePrimops.
require import Real.
require import RevertWithMessage.
require import UInt256.
require import Utils.
require import YulPrimops.
require import Verifier.

module PointAddIntoDest = {
  proc low(p1, p2, dest) =
  {
    var _1, _5, _6, _9, _13, _14;
    _1 <@ Primops.mload(p1);
    Primops.mstore(W256.of_int 0, _1);
    _5 <@ Primops.mload(p1 + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    _6 <@ Primops.mload(p2);
    Primops.mstore(W256.of_int 64, _6);
    _9 <@ Primops.mload(p2 + W256.of_int 32);
    Primops.mstore(W256.of_int 96, _9);
    _13 <@ Primops.gas();
    _14 <@ Primops.staticcall(_13, W256.of_int 6, W256.zero, W256.of_int 128, dest, W256.of_int 64);
    if ((bool_of_uint256 (PurePrimops.iszero _14)))
    {
      RevertWithMessage.low((W256.of_int 30), (W256.of_int STRING (*pointAddIntoDest: ecAdd failed*)));
    }
  }

  proc low'(p1, p2, dest) =
  {
    var _1, _5, _6, _9, _13, _14;
    _1 <@ Primops.mload(p1);
    _5 <@ Primops.mload(p1 + W256.of_int 32);
    _6 <@ Primops.mload(p2);
    _9 <@ Primops.mload(p2 + W256.of_int 32);
    Primops.mstore(W256.of_int 0, _1);
    Primops.mstore(W256.of_int 32, _5);
    Primops.mstore(W256.of_int 64, _6);
    Primops.mstore(W256.of_int 96, _9);
    _13 <@ Primops.gas();
    _14 <@ Primops.staticcall(_13, W256.of_int 6, W256.zero, W256.of_int 128, dest, W256.of_int 64);
    if ((bool_of_uint256 (PurePrimops.iszero _14)))
    {
      RevertWithMessage.low((W256.of_int 30), (W256.of_int STRING (*pointAddIntoDest: ecAdd failed*)));
    }
  }

  proc mid(x1 : int, y1 : int, x2 : int, y2 : int) : int * int = {
    var x, y, x1_F, x2_F, y1_F, y2_F, result;
      x1_F <- ZModField.inzmod x1;
      y1_F <- ZModField.inzmod y1;
      x2_F <- ZModField.inzmod x2;
      y2_F <- ZModField.inzmod y2;
      result <- ecAdd_precompile x1_F y1_F x2_F y2_F;
      (x, y) <- odflt (ZModField.zero, ZModField.zero) result;
      return (ZModField.asint x, ZModField.asint y);
  }
}.

lemma pointAddIntoDest_extracted_equiv_low : equiv [

    Verifier_1261.usr_pointAddIntoDest ~ PointAddIntoDest.low :
      ={arg, glob PointAddIntoDest} ==>
      ={res, glob PointAddIntoDest}
    ].
proof.
  proc.
  seq 24 10: (#pre /\ ={_14}).
  inline*. wp. skip. by progress.
  inline*. wp. skip. by progress.
qed.

lemma usr_pointAddIntoDest_low_matches_low' (p1 p2 dest : uint256) : equiv [
    PointAddIntoDest.low ~ PointAddIntoDest.low':
      ={arg, glob PointAddIntoDest} /\
      arg{1} = (p1, p2, dest) /\
        W256.of_int 128 < p1 /\ W256.of_int 128 < (p1 + W256.of_int 32) /\
        W256.of_int 128 < p2 /\ W256.of_int 128 < (p2 + W256.of_int 32) ==>
      ={res, glob PointAddIntoDest}
    ].
proof.
  proc.
  sim.
  inline*. wp. skip. progress.

  rewrite MemoryMap.load_store_diff.
  have H' : p2{2} + W256.of_int 32 - W256.of_int 64 = p2{2} - W256.of_int 32. smt (@W256).
  rewrite H'. admit.
  admit.

  rewrite MemoryMap.load_store_diff.
  admit.
  admit.

  rewrite MemoryMap.load_store_diff.
  admit.
  admit.

  reflexivity.

  rewrite MemoryMap.load_store_diff.
  admit.
  admit.

  rewrite MemoryMap.load_store_diff.
  admit.
  admit.

  rewrite MemoryMap.load_store_diff.
  admit.
  admit.

  reflexivity.
qed.

lemma PointAddIntoDest_mid_of_low (x1 x2 y1 y2 : int) (p1 p2 dest : uint256) : equiv [
    PointAddIntoDest.low' ~ PointAddIntoDest.mid :
    x1 < p /\ x2 < p /\ y1 < p /\ y2 < p /\
    PurePrimops.mload Primops.memory{1} p1 = W256.of_int x1 /\
    PurePrimops.mload Primops.memory{1} (p1 + W256.of_int 32) = W256.of_int y1 /\
    PurePrimops.mload Primops.memory{1} p2 = W256.of_int x2 /\
    PurePrimops.mload Primops.memory{1} (p2 + W256.of_int 32) = W256.of_int y2 /\
      arg{1} = (p1, p2, dest) /\ arg{2} = (x1, y1, x2, y2)
      ==>
      (
        exists (x y : F),
        ecAdd_precompile (ZModField.inzmod x1) (ZModField.inzmod y1) (ZModField.inzmod x2) (ZModField.inzmod y2) = Some (x, y) /\
        res{2} = (ZModField.asint x, ZModField.asint y) /\
        PurePrimops.mload Primops.memory{1} dest = W256.of_int (ZModField.asint x) /\
        PurePrimops.mload Primops.memory{1} (dest + W256.of_int 32) = W256.of_int (ZModField.asint y)
      ) \/
      (
        ecAdd_precompile (ZModField.inzmod x1) (ZModField.inzmod y1) (ZModField.inzmod x2) (ZModField.inzmod y2) = None /\
        res{2} = (0, 0) /\
        PurePrimops.mload Primops.memory{1} dest = W256.zero /\
        PurePrimops.mload Primops.memory{1} (dest + W256.of_int 32) = W256.zero
      )
    ]. proof.
        exists* Primops.memory{1}.
        elim* => memory.
        proc.
        seq 4 0 :
    (
      #pre /\
      _1{1} = W256.of_int x1 /\
      _5{1} = W256.of_int y1 /\
      _6{1} = W256.of_int x2 /\
      _5{1} = W256.of_int y1 /\
      _9{1} = W256.of_int y2
    ).
    inline *. wp. skip. progress.
    seq 5 0 : 
    (
      x1 < p /\
      x2 < p /\
      y1 < p /\
      y2 < p /\
      (p1{1}, p2{1}, dest{1}) = (p1, p2, dest) /\
      (x1{2}, y1{2}, x2{2}, y2{2}) = (x1, y1, x2, y2) /\
    _1{1} = (of_int x1)%W256 /\
    _5{1} = (of_int y1)%W256 /\
    _6{1} = (of_int x2)%W256 /\
    _5{1} = (of_int y1)%W256 /\ _9{1} = (of_int y2)%W256 /\
    Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory W256.zero _1{1}) (W256.of_int 32) _5{1}) (W256.of_int 64) _6{1}) (W256.of_int 96) _9{1}
    ).
        inline *. wp. skip. progress.
        inline Primops.staticcall. sp.
        rcondf{1} 1. progress. skip. progress. smt (@W256).
        rcondt{1} 1. move=> &m. skip. progress.
        inline Primops.mload. sp.
        (* inline*. wp. skip. progress. *)
