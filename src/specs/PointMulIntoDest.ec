pragma Goals:printall.

require import Array.
require import EllipticCurve.
require import Field.
require import Logic.
require import Memory.
require import PurePrimops.
require import Real.
require import RevertWithMessage.
require import UInt256.
require import Utils.
require import YulPrimops.
require import Verifier.

import MemoryMap.

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
    x_F <- FieldQ.inF x;
    y_F <- FieldQ.inF y;
    result <- ecMul_precompile x_F y_F s;
    return (omap F_to_int_point result);
  }

  proc high_field(p: FieldQ.F*FieldQ.F, s : FieldR.F) : (FieldQ.F * FieldQ.F) option =
  {
    return ecMul_precompile p.`1 p.`2 (FieldR.asint s);
  }

  proc high(p: g, s: FieldR.F): g = {
    return s * p;
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

lemma pointMulIntoDest_low_pspec_revert:
    phoare [ PointMulIntoDest.low :
    Primops.reverted ==>
    Primops.reverted
    ] = 1%r.
    proof.
      proc.
      inline Primops.mload Primops.mstore Primops.gas.
      sp.
      inline*. wp. skip. by progress.
    qed.
    
op pointMulIntoDest_memory_footprint (mem_0: mem) (dest: uint256) (point result: int*int) (factor: int) =
    let mem_1 = store mem_0 W256.zero (W256.of_int point.`1) in
    let mem_2 = store mem_1 (W256.of_int 32) (W256.of_int point.`2) in
    let mem_3 = store mem_2 (W256.of_int 64) (W256.of_int factor) in
    let mem_4 = store mem_3 dest (W256.of_int result.`1) in
    store mem_4 (dest + W256.of_int 32) (W256.of_int result.`2).

lemma pointMulIntoDest_low_equiv_mid (x1v y1v sv : int) (p1u destu : uint256) (memory0 : MemoryMap.mem) : equiv [
    PointMulIntoDest.low ~ PointMulIntoDest.mid :
    Primops.memory{1} = memory0 /\
      0 <= x1v < FieldQ.p /\ 0 <= y1v < FieldQ.p /\ 0 <= sv < W256.modulus /\
      (of_int 128)%W256 <= p1u /\
      (of_int 64)%W256 <= -p1u /\
      (of_int 128)%W256 <= p1u + (of_int 32)%W256 /\
      (of_int 32)%W256 <= - (p1u + (of_int 32)%W256) /\
    PurePrimops.mload memory0 p1u = W256.of_int x1v /\
    PurePrimops.mload memory0 (p1u + W256.of_int 32) = W256.of_int y1v /\
      arg{1} = (p1u, W256.of_int sv, destu) /\ arg{2} = (x1v, y1v, sv) /\ !Primops.reverted{1}
      ==>
        exists (memory_F : MemoryMap.mem),
      memory_F = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero (W256.of_int x1v)) (W256.of_int 32) (W256.of_int y1v)) (W256.of_int 64) (W256.of_int sv)  /\
      (
        ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) /\
        exists (x y : FieldQ.F),
        ecMul_precompile (FieldQ.inF x1v) (FieldQ.inF y1v) sv = Some (x, y) /\
        res{2} = Some (FieldQ.asint x, FieldQ.asint y) /\
        Primops.memory{1} = store (store memory_F destu (W256.of_int (FieldQ.asint x))) (destu + W256.of_int 32) (W256.of_int (FieldQ.asint y)) /\
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
      0 <= x1v < FieldQ.p /\ 0 <= y1v < FieldQ.p /\ 0 <= sv < W256.modulus /\
      (point{1}, s{1}, dest{1}) = (p1u, (of_int sv)%W256, destu) /\
      (x{2}, y{2}, s{2}) = (x1v, y1v, sv) /\ !Primops.reverted{1} /\
      x_F{2} = FieldQ.inF x1v /\ y_F{2} = FieldQ.inF y1v
    ).
        inline *. wp. skip. progress.

        rewrite MemoryMap.load_store_diff. rewrite uint256_sub_zero_eq.
        apply (uint256_le_le_trans _ (W256.of_int 128) _). smt (@UInt256). exact H7.
        rewrite uint256_zero_sub_eq_sub. exact H8. rewrite H9 H10. reflexivity.

        case (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv)).
        exists* Primops.memory{1}.
        elim*=> memory_F.
        seq 1 1 : 
    (
      0 <= x1v < FieldQ.p /\ 0 <= y1v < FieldQ.p /\ 0 <= sv < W256.modulus /\
      (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv)) /\
      memory_F = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero (W256.of_int x1v)) (W256.of_int 32) (W256.of_int y1v)) (W256.of_int 64) (W256.of_int sv) /\
        exists (x' y' : FieldQ.F),
        EllipticCurve.ecMul_precompile (FieldQ.inF x1v) (FieldQ.inF y1v) sv = Some (x', y') /\
        Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore memory_F destu (W256.of_int (FieldQ.asint x'))) (destu + W256.of_int 32) (W256.of_int (FieldQ.asint y')) /\
        result{2} = Some (x',y') /\ 
        (point{1}, s{1}, dest{1}) = (p1u, (of_int sv)%W256, destu) /\
        (x{2}, y{2}, s{2}) = (x1v, y1v, sv) /\ !Primops.reverted{1} /\ _10{1} = W256.one /\
        x_F{2} = FieldQ.inF x1v /\ y_F{2} = FieldQ.inF y1v
      ).

          call {1} (ConcretePrimops.staticcall_ec_mul_pspec memory_F (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) W256.zero destu).
      wp. skip. progress. 
      
          rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
          rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
          rewrite MemoryMap.load_store_same. reflexivity.

          rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
          rewrite MemoryMap.load_store_same. reflexivity.

          rewrite MemoryMap.load_store_same. reflexivity.

          have J : exists (p : FieldQ.F * FieldQ.F), EllipticCurve.ecMul_precompile
      ((FieldQ.inF (to_uint ((of_int x{2})%W256, (of_int y{2})%W256).`1)))
      ((FieldQ.inF (to_uint ((of_int x{2})%W256, (of_int y{2})%W256).`2)))
      (W256.to_uint (W256.of_int s{2}))
      = Some p. apply exists_of_is_some. smt ().
        case J.
      move=> pt.
        pose x' := pt.`1.
        pose y' := pt.`2.
        progress. exists x'. exists y'.
        progress. have EQ : Some (x', y') = Some pt. smt (). rewrite EQ -H12. congr.
        rewrite W256.to_uint_small. progress. 
        apply (lt_trans _ FieldQ.p _). exact H0. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by progress.
        reflexivity.
        rewrite W256.to_uint_small. progress.
        apply (lt_trans _ FieldQ.p _). exact H2. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by progress.
        reflexivity.
        rewrite W256.to_uint_small. progress.
        reflexivity.
        smt ().
        have EQ : Some (x', y') = Some pt. smt (). rewrite EQ -H12. congr.
        rewrite W256.to_uint_small. progress. 
        apply (lt_trans _ FieldQ.p _). exact H0. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by progress.
        reflexivity.
        rewrite W256.to_uint_small. progress. 
        apply (lt_trans _ FieldQ.p _). exact H2. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by progress.
        reflexivity.
        rewrite W256.to_uint_small. progress. 
        reflexivity.
        smt ().

        rcondf {1} 1. progress. skip. progress. smt (). skip. progress.
      exists ((store
     ((store ((store memory0 W256.zero ((of_int x{2}))%W256))
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
     rewrite to_uint_small in H12. progress. apply (lt_trans _ FieldQ.p _). exact H0. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by progress.
     rewrite to_uint_small in H12. progress. apply (lt_trans _ FieldQ.p _). exact H2. rewrite -Constants.q_eq_fieldq_p /Constants.Q. by progress.
     rewrite to_uint_small in H12. progress.

     apply eq_none_of_is_none.
 
     apply H12.

     progress.

     smt ().
 
     rcondt {1} 1.
     progress. skip. progress. smt.
     inline *. wp. skip. progress.
qed.

lemma pointMulIntoDest_mid_equiv_high_field:
equiv [
    PointMulIntoDest.mid ~ PointMulIntoDest.high_field:
      x{1} = (F_to_int_point p{2}).`1 /\
      y{1} = (F_to_int_point p{2}).`2 /\
      s{1} = FieldR.asint s{2} ==>
      (
        (res{1} = None /\ res{2} = None) \/
        (exists (ret_int: int*int, ret_f: FieldQ.F*FieldQ.F),
          res{1} = Some ret_int /\ res{2} = Some ret_f /\
          ret_int = F_to_int_point ret_f
        )
      )
    ].
    proof.
      proc.
      wp. skip.
      progress.
      do rewrite F_to_int_point_inzmod_1.
      do rewrite F_to_int_point_inzmod_2.
      case (ecMul_precompile p{2}.`1 p{2}.`2 (FieldR.asint s{2})).
      by progress.
    move=> p_mul.
      progress.
      exists (F_to_int_point p_mul); exists (p_mul).
      by progress.
    qed.

lemma pointMulIntoDest_high_field_equiv_high:
equiv [
    PointMulIntoDest.high_field ~ PointMulIntoDest.high:
      aspoint_G1 p{2} = p{1} /\
      s{1} = s{2} ==>
      res{1} = Some (aspoint_G1 res{2})
    ].
    proof.
      proc.
      skip.
      progress.
      by rewrite - (ecMul_def (aspoint_G1 p{2}).`1 (aspoint_G1 p{2}).`2 (FieldR.asint s{2}) p{2}); [smt () | rewrite FieldR.asintK; reflexivity].
    qed.

lemma pointMulIntoDest_mid_equiv_high:
equiv [
    PointMulIntoDest.mid ~ PointMulIntoDest.high:
      x{1} = (F_to_int_point (aspoint_G1 p{2})).`1 /\
      y{1} = (F_to_int_point (aspoint_G1 p{2})).`2 /\    
      s{1} = FieldR.asint s{2} ==>
      res{1} = Some (F_to_int_point (aspoint_G1 res{2}))
    ].
    proof.
      transitivity PointMulIntoDest.high_field
    (
      x{1} = (F_to_int_point p{2}).`1 /\
      y{1} = (F_to_int_point p{2}).`2 /\
      s{1} = FieldR.asint s{2} ==>
      (
        (res{1} = None /\ res{2} = None) \/
        (exists (ret_int: int*int, ret_f: FieldQ.F*FieldQ.F),
          res{1} = Some ret_int /\ res{2} = Some ret_f /\
          ret_int = F_to_int_point ret_f
        )
      )
    )
    (
      aspoint_G1 p{2} = p{1} /\
      s{1} = s{2} ==>
      res{1} = Some (aspoint_G1 res{2})
    ).
        by progress; exists (aspoint_G1 p{2}, s{2}); progress.
        by progress; case H; progress.
        exact pointMulIntoDest_mid_equiv_high_field.
        exact pointMulIntoDest_high_field_equiv_high.
    qed. 
