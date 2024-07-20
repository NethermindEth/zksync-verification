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

module PointMulIntoDest = {
  proc low(point, s, dest) =
  {
    var _1, _5,  _9, _10;
    _1 <@ Primops.mload(point);
    Primops.mstore(W256.zero, _1);
    _5 <@ Primops.mload(point + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    Primops.mstore(W256.of_int 64, s);
    _9 <@ Primops.gas();
    _10 <@ Primops.staticcall(_9, W256.of_int 7, W256.zero, W256.of_int 96, dest, W256.of_int 64);
    if (bool_of_uint256 (PurePrimops.iszero(_10)))
    {
      RevertWithMessage.low(W256.of_int 30, W256.zero);
    }
  }

  proc mid(x : int, y : int, s : int) : (int * int) option =
  {
    var x_F, y_F, result;
    x_F <- ZModField.inzmod x;
    y_F <- ZModField.inzmod y;
    result <- ecMul_precompile x_F y_F s;
    return (omap F_to_uint256_point result);
  }
}.

lemma pointMulIntoDest_extracted_equiv_low : equiv [
    Verifier_1261.usr_pointMulIntoDest ~ PointMulIntoDest.low :
      ={arg, glob PointMulIntoDest} ==>
      ={res, glob PointMulIntoDest}
    ].
proof.
  proc.
  seq 17 7: (#pre /\ ={_10}).
  inline*. wp. skip. by progress.
  inline*. wp. skip. by progress.
qed.


lemma PointAddIntoDest_mid_of_low (x1v y1v sv : int) (p1u destu : uint256) (memory0 : MemoryMap.mem) : equiv [
    PointMulIntoDest.low ~ PointMulIntoDest.mid :
    Primops.memory{1} = memory0 /\
      0 <= x1v < p /\ 0 <= y1v < p /\ 0 <= sv < W256.modulus /\
      (of_int 128)%W256 < p1u /\
      (of_int 128)%W256 < -p1u /\
      (of_int 128)%W256 < p1u + (of_int 32)%W256 /\
      (of_int 128)%W256 < - (p1u + (of_int 32)%W256) /\
    PurePrimops.mload memory0 p1u = W256.of_int x1v /\
    PurePrimops.mload memory0 (p1u + W256.of_int 32) = W256.of_int y1v /\
      arg{1} = (p1u, W256.of_int sv, destu) /\ arg{2} = (x1v, y1v, sv) /\ !Primops.reverted{1}
      ==>
        exists (memory_F : MemoryMap.mem),
      memory_F = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero (W256.of_int x1v)) (W256.of_int 32) (W256.of_int y1v)) (W256.of_int 64) (W256.of_int sv)  /\
      (
        ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) /\
        exists (x y : F),
        ecMul_precompile (ZModField.inzmod x1v) (ZModField.inzmod y1v) sv = Some (x, y) /\
        res{2} = Some (ZModField.asint x, ZModField.asint y) /\
        Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore memory_F destu (W256.of_int (ZModField.asint x))) (destu + W256.of_int 32) (W256.of_int (ZModField.asint y)) /\
        !Primops.reverted{1}
      ) \/
      (
        !ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) /\
        res{2} = None /\
        Primops.reverted{1}
      )
    ]. proof.
        proc.
        seq 6 2 :
    (
      Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero (W256.of_int x1v)) (W256.of_int 32) (W256.of_int y1v)) (W256.of_int 64) (W256.of_int sv) /\
      0 <= x1v < p /\ 0 <= y1v < p /\ 0 <= sv < W256.modulus /\
      (point{1}, s{1}, dest{1}) = (p1u, (of_int sv)%W256, destu) /\
      (x{2}, y{2}, s{2}) = (x1v, y1v, sv) /\ !Primops.reverted{1} /\
      x_F{2} = ZModField.inzmod x1v /\ y_F{2} = ZModField.inzmod y1v
    ).
        inline *. wp. skip. progress.

        rewrite MemoryMap.load_store_diff. rewrite uint256_sub_zero_eq.
        apply (uint256_le_lt_trans _ (W256.of_int 128) _). smt (@UInt256). exact H7.
        rewrite uint256_zero_sub_eq_sub. apply (uint256_le_lt_trans _ (W256.of_int 128) _). smt (@UInt256). exact H8. rewrite H9 H10. reflexivity.

        case (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv)).
        exists* Primops.memory{1}.
        elim*=> memory_F.
        seq 1 1 : 
    (
      0 <= x1v < p /\ 0 <= y1v < p /\ 0 <= sv < W256.modulus /\
      (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv)) /\
      memory_F = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero (W256.of_int x1v)) (W256.of_int 32) (W256.of_int y1v)) (W256.of_int 64) (W256.of_int sv) /\
        exists (x' y' : F),
        EllipticCurve.ecMul_precompile (ZModField.inzmod x1v) (ZModField.inzmod y1v) sv = Some (x', y') /\
        Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore memory_F destu (W256.of_int (ZModField.asint x'))) (destu + W256.of_int 32) (W256.of_int (ZModField.asint y')) /\
        result{2} = Some (x',y') /\ 
        (point{1}, s{1}, dest{1}) = (p1u, (of_int sv)%W256, destu) /\
        (x{2}, y{2}, s{2}) = (x1v, y1v, sv) /\ !Primops.reverted{1} /\ _10{1} = W256.one /\
        x_F{2} = ZModField.inzmod x1v /\ y_F{2} = ZModField.inzmod y1v
      ).

          call {1} (ConcretePrimops.staticcall_ec_mul_pspec memory_F (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) W256.zero destu).
      wp. skip. progress. 
      
          rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
          rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
          rewrite MemoryMap.load_store_same. reflexivity.

          rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
          rewrite MemoryMap.load_store_same. reflexivity.

          rewrite MemoryMap.load_store_same. reflexivity.

          have J : exists (p : F * F), EllipticCurve.ecMul_precompile
      ((ZModField.inzmod (to_uint ((of_int x{2})%W256, (of_int y{2})%W256).`1)))
      ((ZModField.inzmod (to_uint ((of_int x{2})%W256, (of_int y{2})%W256).`2)))
      (W256.to_uint (W256.of_int s{2}))
      = Some p. apply exists_of_is_some. smt ().
        case J.
      move=> pt.
        pose x' := pt.`1.
        pose y' := pt.`2.
        progress. exists x'. exists y'.
        progress. have EQ : Some (x', y') = Some pt. smt (). rewrite EQ -H12. congr.
        rewrite W256.to_uint_small. progress. 
        apply (lt_trans _ p _). exact H0. exact p_lt_W256_mod.
        reflexivity.
        rewrite W256.to_uint_small. progress.
        apply (lt_trans _ p _). exact H2. exact p_lt_W256_mod.
        reflexivity.
        rewrite W256.to_uint_small. progress.
        reflexivity.
        smt ().
        have EQ : Some (x', y') = Some pt. smt (). rewrite EQ -H12. congr.
        rewrite W256.to_uint_small. progress. 
        apply (lt_trans _ p _). exact H0. exact p_lt_W256_mod.
        reflexivity.
        rewrite W256.to_uint_small. progress. 
        apply (lt_trans _ p _). exact H2. exact p_lt_W256_mod.
        reflexivity.
        rewrite W256.to_uint_small. progress. 
        reflexivity.
        smt ().

        rcondf {1} 1. progress. skip. progress. smt (). skip. progress.
      exists ((PurePrimops.mstore
     ((PurePrimops.mstore ((PurePrimops.mstore memory0 W256.zero ((of_int x{2}))%W256))
         ((W256.of_int 32)) ((W256.of_int y{2}))))
     ((W256.of_int 64)) ((W256.of_int s{2})))).
       progress. exists x'. exists y'. progress.
       exists* Primops.memory{1}.
       elim*=> memory_F.
       seq 1 1 :
 (
   !ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) /\ result{2} = None /\ _10{1} = W256.zero
 ).
       
     call {1} (ConcretePrimops.staticcall_ec_mul_pspec memory_F (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) W256.zero destu).
     wp. skip. progress.

     rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
     rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
     rewrite MemoryMap.load_store_same. reflexivity.

     rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
     rewrite MemoryMap.load_store_same. reflexivity.

     rewrite MemoryMap.load_store_same. reflexivity.

     have tmp  : (W256.of_int x{2}, W256.of_int y{2}).`1 = W256.of_int x{2}. smt ().
     have tmp' : (W256.of_int x{2}, W256.of_int y{2}).`2 = W256.of_int y{2}. smt ().
     have H12 := ConcretePrimops.ecMul_precomp_is_none_of_should_not_succeed (W256.of_int x{2}, W256.of_int y{2}) (W256.of_int s{2}).
     rewrite tmp tmp' in H12.
     rewrite to_uint_small in H12. progress. apply (lt_trans _ p _). exact H0. exact p_lt_W256_mod.
     rewrite to_uint_small in H12. progress. apply (lt_trans _ p _). exact H2. exact p_lt_W256_mod.
     rewrite to_uint_small in H12. progress.

     apply eq_none_of_is_none.
 
     apply H12.

     progress.

     smt ().
 
     rcondt {1} 1.
     progress. skip. progress. smt.
     inline *. wp. skip. progress.
qed.

      
