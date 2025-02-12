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

module PointMulAndAddIntoDest = {
  proc low(point, s, dest) =
  {
    var _1, _5, _9, success, _10, _12, _15, _16;
    _1 <@ Primops.mload(point);
    Primops.mstore(W256.zero, _1);
    _5 <@ Primops.mload(point + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    Primops.mstore(W256.of_int 64, s);
    _9 <@ Primops.gas();
    success <@ Primops.staticcall(_9, W256.of_int 7, W256.zero, W256.of_int 96, W256.zero, W256.of_int 64);
    _10 <@ Primops.mload(dest);
    Primops.mstore(W256.of_int 64, _10);
    _12 <@ Primops.mload(dest + W256.of_int 32);
    Primops.mstore(W256.of_int 96, _12);
    _15 <@ Primops.gas();
    _16 <@ Primops.staticcall(_15, W256.of_int 6, W256.zero, W256.of_int 128, dest, W256.of_int 64);
    success <- (PurePrimops.bit_and success _16);
    if ((bool_of_uint256 (PurePrimops.iszero success)))
    {
      RevertWithMessage.low(W256.of_int 22, W256.of_int STRING);
    }
  }

  proc mid(x1 : int, y1 : int, s : int, x2 : int, y2 : int) : (int * int) option = {
      var x1_F, y1_F, x2_F, y2_F, mresult, mresult', aresult, fresult; 
      x1_F <- FieldQ.inF x1;
      y1_F <- FieldQ.inF y1;
      mresult <- ecMul_precompile x1_F y1_F s;
      if (is_some mresult) {
         x2_F <- FieldQ.inF x2;
         y2_F <- FieldQ.inF y2;
         mresult' <- odflt (FieldQ.zero, FieldQ.zero) mresult;
         aresult  <- ecAdd_precompile mresult'.`1 mresult'.`2 x2_F y2_F; 
         fresult <- omap F_to_int_point aresult;
      } else {
          fresult <- None;
      }
      return fresult;
  }

  proc high_field(p1 : FieldQ.F*FieldQ.F, s : FieldR.F, p2 : FieldQ.F*FieldQ.F) : (FieldQ.F*FieldQ.F) option = {
      var mresult, mresult', fresult; 
      mresult <- ecMul_precompile p1.`1 p1.`2 (FieldR.asint s);
      if (is_some mresult) {
        mresult' <- odflt (FieldQ.zero, FieldQ.zero) mresult;
        fresult  <- ecAdd_precompile mresult'.`1 mresult'.`2 p2.`1 p2.`2; 
      } else {
        fresult <- None;
      }
      return fresult;
  }

  proc high(p1: g, s: FieldR.F, p2: g): g = {
      return (s * p1) + p2; 
  }
}.

lemma pointMulAndAddIntoDest_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_pointMulAndAddIntoDest ~ PointMulAndAddIntoDest.low :
      ={arg, glob PointMulAndAddIntoDest} ==>
      ={res, glob PointMulAndAddIntoDest}
    ].
proof.
  proc.
  seq 20 9: (#pre /\ ={_1} /\ _2{1} = W256.zero /\ _3{1} = W256.of_int 32 /\  _4{1} = usr_point{1} + _3{1} /\
            _6{1} = W256.of_int 64 /\ _7{1} = W256.of_int 96 /\ _8{1} = W256.of_int 7 /\ ={_5, _9, _10} /\ usr_success{1} = success{2}).
  inline*. wp. skip. by progress.
  sp.
  seq 9 4: (#pre /\ ={_12} /\ _13{1} = W256.of_int 128 /\ _14{1} = W256.of_int 6 /\ ={_15, _16}).
  inline*. wp. skip. by progress.
  inline*. wp. skip. by progress.
qed.

lemma pointMulAndAddIntoDest_low_pspec_revert:
    phoare [ PointMulAndAddIntoDest.low :
    Primops.reverted ==>
    Primops.reverted
    ] = 1%r.
    proof.
      proc.
      inline Primops.mload Primops.mstore Primops.gas.
      sp.
      inline*. wp. skip. by progress.
    qed.
  
lemma pointMulAndAddIntoDest_low_equiv_mid (x1v y1v x2v y2v sv : int) (p1u destu : uint256) (memory0 : MemoryMap.mem) : equiv [
    PointMulAndAddIntoDest.low ~ PointMulAndAddIntoDest.mid :
    Primops.memory{1} = memory0 /\
      0 <= x1v < FieldQ.p /\ 0 <= y1v < FieldQ.p /\ 0 <= sv < W256.modulus /\ 0 <= x2v < FieldQ.p /\ 0 <= y2v < FieldQ.p /\
      (of_int 128)%W256 <= p1u /\
      (of_int 64)%W256 <= -p1u /\
      (of_int 128)%W256 <= p1u + (of_int 32)%W256 /\
      (of_int 32)%W256 <= - (p1u + (of_int 32)%W256) /\
      (of_int 128)%W256 <= destu /\
      (of_int 64)%W256 <= -destu /\
      (of_int 128)%W256 <= destu + (of_int 32)%W256 /\
      (of_int 32)%W256 <= - (destu + (of_int 32)%W256) /\
    PurePrimops.mload memory0 p1u = W256.of_int x1v /\
    PurePrimops.mload memory0 (p1u + W256.of_int 32) = W256.of_int y1v /\
    PurePrimops.mload memory0 destu = W256.of_int x2v /\
    PurePrimops.mload memory0 (destu + W256.of_int 32) = W256.of_int y2v /\
      arg{1} = (p1u, W256.of_int sv, destu) /\ arg{2} = (x1v, y1v, sv, x2v, y2v) /\ !Primops.reverted{1}
      ==>
      (
        ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) /\
        exists (x y : FieldQ.F),
        ecMul_precompile (FieldQ.inF x1v) (FieldQ.inF y1v) sv = Some (x, y) /\
        (
          ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int (FieldQ.asint x), W256.of_int (FieldQ.asint y)) (W256.of_int x2v, W256.of_int y2v) /\
          exists (x' y' : FieldQ.F),
          ecAdd_precompile x y (FieldQ.inF x2v) (FieldQ.inF y2v) = Some (x', y') /\
          res{2} = Some( F_to_int_point (x', y')) /\
          Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero (W256.of_int (FieldQ.asint x))) (W256.of_int 32) (W256.of_int (FieldQ.asint y))) (W256.of_int 64) (W256.of_int x2v)) (W256.of_int 96) (W256.of_int y2v)) destu (W256.of_int (FieldQ.asint x'))) (destu + W256.of_int 32) (W256.of_int (FieldQ.asint y')) /\ 
          !Primops.reverted{1}
        )
        \/
        (
          !ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int (FieldQ.asint x), W256.of_int (FieldQ.asint y)) (W256.of_int x2v, W256.of_int y2v) /\
          res{2} = None /\
          Primops.reverted{1}
        )
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
      0 <= x1v < FieldQ.p /\ 0 <= y1v < FieldQ.p /\ 0 <= sv < W256.modulus /\ 0 <= x2v < FieldQ.p /\ 0 <= y2v < FieldQ.p /\
      (of_int 128)%W256 <= destu /\
      (of_int 64)%W256 <= -destu /\
      (of_int 128)%W256 <= destu + (of_int 32)%W256 /\
      (of_int 32)%W256 <= - (destu + (of_int 32)%W256) /\
      PurePrimops.mload memory0 destu = W256.of_int x2v /\
      PurePrimops.mload memory0 (destu + W256.of_int 32) = W256.of_int y2v /\
      Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero (W256.of_int x1v)) (W256.of_int 32) (W256.of_int y1v)) (W256.of_int 64) (W256.of_int sv) /\
      x1_F{2} = FieldQ.inF x1v /\ y1_F{2} = FieldQ.inF y1v /\
      (point{1}, s{1}, dest{1}) = (p1u, W256.of_int sv, destu) /\ (x1{2}, y1{2}, s{2}, x2{2}, y2{2}) = (x1v, y1v, sv, x2v, y2v) /\ !Primops.reverted{1}
    ).
        inline *. wp. skip. progress. congr.

        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite H17 H18. reflexivity.

        case (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv)).

        seq 1 1 :
    (
      (0 <= x1v && x1v < FieldQ.p) /\
      (0 <= y1v && y1v < FieldQ.p) /\
      (0 <= sv && sv < W256.modulus) /\
      (0 <= x2v && x2v < FieldQ.p) /\
      (0 <= y2v && y2v < FieldQ.p) /\
        W256.of_int 128 <= destu /\
        W256.of_int 64  <= -destu /\
        W256.of_int 128 <= destu + (W256.of_int 32) /\
        W256.of_int 32  <= - (destu + (W256.of_int 32)) /\
        PurePrimops.mload memory0 destu = W256.of_int x2v /\
        PurePrimops.mload memory0 (destu + (W256.of_int 32)) = W256.of_int y2v /\
      x1_F{2} = FieldQ.inF x1v /\
      y1_F{2} = FieldQ.inF y1v /\
        (point{1}, s{1}, dest{1}) = (p1u, W256.of_int sv, destu) /\
        (x1{2}, y1{2}, s{2}, x2{2}, y2{2}) = (x1v, y1v, sv, x2v, y2v) /\
          !Primops.reverted{1} /\
        (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v)
          (W256.of_int sv)) /\
            exists (x y : FieldQ.F),
        ecMul_precompile x1_F{2} y1_F{2} sv = Some (x, y) /\
        success{1} = W256.one /\ mresult{2} = Some (x, y) /\
            Primops.memory{1} =
        (PurePrimops.mstore
          ((PurePrimops.mstore ((PurePrimops.mstore memory0 W256.zero ((W256.of_int (FieldQ.asint x)))))
              (W256.of_int 32) (W256.of_int (FieldQ.asint y))))
          (W256.of_int 64) (W256.of_int sv))
      ).

          exists* Primops.memory{1}.
          elim*=> memory1.
          seq 0 0 :
      (
        exists (x y : FieldQ.F),
        ecMul_precompile (FieldQ.inF x1v) (FieldQ.inF y1v) sv = Some (x, y) /\
        memory1 = Primops.memory{1} /\
        ((0 <= x1v && x1v < FieldQ.p) /\
          (0 <= y1v && y1v < FieldQ.p) /\
          (0 <= sv && sv < W256.modulus) /\
          (0 <= x2v && x2v < FieldQ.p) /\
          (0 <= y2v && y2v < FieldQ.p) /\
          (of_int 128)%W256 <= destu /\
          (of_int 64)%W256 <= -destu /\
          (of_int 128)%W256 <= destu + (W256.of_int 32) /\
          (of_int 32)%W256 <= - (destu + (W256.of_int 32)) /\
          PurePrimops.mload memory0 destu = W256.of_int x2v /\
          PurePrimops.mload memory0 (destu + (W256.of_int 32)) = (W256.of_int y2v) /\
            Primops.memory{1} =
          (PurePrimops.mstore
            ((PurePrimops.mstore ((PurePrimops.mstore memory0 W256.zero ((of_int x1v))%W256))
                ((of_int 32))%W256 ((of_int y1v))%W256))%PurePrimops
            ((of_int 64))%W256 ((of_int sv))%W256)%PurePrimops /\
          x1_F{2} = (FieldQ.inF x1v) /\
          y1_F{2} = (FieldQ.inF y1v) /\
          (point{1}, s{1}, dest{1}) = (p1u, (of_int sv)%W256, destu) /\
          (x1{2}, y1{2}, s{2}, x2{2}, y2{2}) = (x1v, y1v, sv, x2v, y2v) /\
            !Primops.reverted{1}) /\
        (ConcretePrimops.staticcall_ec_mul_should_succeed ((of_int x1v)%W256, (of_int y1v)%W256)
          ((of_int sv))%W256)
      ). skip. progress. 
          have J0 := exists_of_is_some _ (ConcretePrimops.ecMul_precomp_is_some_of_should_succeed _ _ H16).
          case J0. move=>pt J0. pose x := pt.`1. pose y := pt.`2. exists x. exists y.
          progress.
          have J0' : ecMul_precompile
      (FieldQ.inF (to_uint (W256.of_int x1{2})))
      (FieldQ.inF (to_uint (W256.of_int y1{2})))
      (to_uint (W256.of_int s{2})) =
        Some pt. smt ().
        rewrite to_uint_small in J0'. progress. apply (lt_trans _ FieldQ.p _). exact H0. rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
        rewrite to_uint_small in J0'. progress. apply (lt_trans _ FieldQ.p _). exact H2. rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
        rewrite to_uint_small in J0'. progress. smt ().
        elim* => x y.
      
        call {1} (ConcretePrimops.staticcall_ec_mul_pspec memory1 (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) W256.zero W256.zero). wp. skip. progress. 

          rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite MemoryMap.load_store_same. reflexivity.

          rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite MemoryMap.load_store_same. reflexivity.

          rewrite MemoryMap.load_store_same. reflexivity.

        exists x. exists y. progress. smt ().
        have J1 :
      (
        memory_L =
     (PurePrimops.mstore
        ((PurePrimops.mstore
            ((PurePrimops.mstore
                ((PurePrimops.mstore
                    ((PurePrimops.mstore memory0 W256.zero ((of_int x1{2}))%W256))
                    ((of_int 32))%W256 ((of_int y1{2}))%W256))%PurePrimops
                ((of_int 64))%W256 ((of_int s{2}))%W256))%PurePrimops
            W256.zero
            ((ConcretePrimops.ecMul_precompile_unsafe_cast
                ((of_int x1{2})%W256, (of_int y1{2})%W256)
                ((of_int s{2}))%W256)).`1))%PurePrimops
        ((of_int 32))%W256
        ((ConcretePrimops.ecMul_precompile_unsafe_cast
            ((of_int x1{2})%W256, (of_int y1{2})%W256) ((of_int s{2}))%W256)).`2)%PurePrimops
    ). smt ().

        rewrite J1.
        rewrite -(MemoryMap.store_store_swap_diff _ W256.zero). smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite -(MemoryMap.store_store_swap_diff _ W256.zero). smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite MemoryMap.store_store_same.

        rewrite -(MemoryMap.store_store_swap_diff _ (W256.of_int 32)). smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite MemoryMap.store_store_same. 
        rewrite /ecMul_precompile_unsafe_cast. simplify.
        rewrite to_uint_small. progress. apply (lt_trans _ FieldQ.p _). exact H1. rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
        rewrite to_uint_small. progress. apply (lt_trans _ FieldQ.p _). exact H3. rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
        rewrite to_uint_small. progress.

        rewrite H. progress.

        rcondt {2} 1. progress.

        seq 5 3 :
    (
      exists (x y : FieldQ.F),
      (0 <= x1v && x1v < FieldQ.p) /\
      (0 <= y1v && y1v < FieldQ.p) /\
      (0 <= sv && sv < W256.modulus) /\
      (0 <= x2v && x2v < FieldQ.p) /\
      (0 <= y2v && y2v < FieldQ.p) /\
      x2_F{2} = FieldQ.inF x2v /\
      y2_F{2} = FieldQ.inF y2v /\
      (point{1}, s{1}, dest{1}) = (p1u, W256.of_int sv, destu) /\
      (x1{2}, y1{2}, s{2}, x2{2}, y2{2}) = (x1v, y1v, sv, x2v, y2v) /\
        !Primops.reverted{1} /\
      (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v)
        (W256.of_int sv)) /\
          ecMul_precompile (FieldQ.inF x1v) (FieldQ.inF y1v) sv = Some (x, y) /\
      success{1} = W256.one /\
      mresult'{2} = (x, y) /\
          Primops.memory{1} =
          PurePrimops.mstore (PurePrimops.mstore
        (PurePrimops.mstore
          (PurePrimops.mstore memory0 W256.zero (W256.of_int (FieldQ.asint x)))
          (W256.of_int 32) (W256.of_int (FieldQ.asint y)))
        (W256.of_int 64) (W256.of_int x2v)) (W256.of_int 96) (W256.of_int y2v)
    ).

          inline *. wp. skip. progress.
          exists x. exists y.
          progress.

      
        rewrite MemoryMap.load_store_diff.
    
        rewrite Utils.uint256_cast_sub.
        apply uint256_le_of_le.
        rewrite to_uint_small. smt ().
        rewrite to_uint_small. smt (@IntDiv @W256).
        rewrite to_uint_small. smt ().
        have H9' : 128 <= to_uint dest{1}. smt (@W256 @Utils).
        have J0 : to_uint dest{1} < W256.modulus. apply uint256_size.
        rewrite mod_eq_self. smt (). smt (). apply sub_mono_lt. smt (). exact J0. smt ().

        rewrite Utils.uint256_cast_sub.
        apply uint256_le_of_le.
        rewrite to_uint_small. smt ().
        rewrite to_uint_small. smt ().
        rewrite to_uint_small. smt ().
        have H9' : 128 <= to_uint dest{1}. smt (@W256 @Utils).
        have J0 : to_uint dest{1} < W256.modulus. apply uint256_size.
        rewrite mod_plus.
        rewrite mod_eq_self. smt (). smt. smt. smt.

        rewrite MemoryMap.load_store_diff.

        rewrite Utils.uint256_cast_sub.
        apply uint256_le_of_le.
        rewrite to_uint_small. smt ().
        rewrite to_uint_small. smt (@IntDiv @W256).
        have H9' : 128 <= to_uint dest{1}. smt (@W256 @Utils).
        have J0 : to_uint dest{1} < W256.modulus. apply uint256_size.
        rewrite mod_eq_self. smt (). smt (). smt. smt ().

        rewrite Utils.uint256_cast_sub.
        apply uint256_le_of_le.
        rewrite to_uint_small. smt ().
        rewrite to_uint_small. smt ().
        have H9' : 128 <= to_uint dest{1}. smt (@W256 @Utils).
        have J0 : to_uint dest{1} < W256.modulus. apply uint256_size.
        rewrite mod_plus.
        rewrite mod_eq_self. smt (). smt. smt. smt.

        rewrite MemoryMap.load_store_diff.

        smt (@W256 @Utils).
        smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.

        have J0 : dest{1} + (of_int 32)%W256 - (of_int 64)%W256 = dest{1} - (of_int 32)%W256. smt (@Utils @W256).
        rewrite J0.
        rewrite Utils.uint256_cast_sub.
        apply uint256_le_of_le.
        rewrite to_uint_small. smt ().
        rewrite to_uint_small. smt (@IntDiv @W256).
        have H9' : 128 <= to_uint dest{1}. smt (@W256 @Utils).
        have J1 : to_uint dest{1} < W256.modulus. apply uint256_size.
        rewrite mod_eq_self. smt (). smt (). smt. smt ().

        have K0 : (of_int 64)%W256 - (dest{1} + (of_int 32)%W256) = (W256.of_int 32) - dest{1}.
        rewrite uint256_distrib_sub. smt (@W256 @Utils).
        rewrite K0.
        rewrite Utils.uint256_cast_sub.
        apply uint256_le_of_le.
        rewrite to_uint_small. smt ().
        rewrite to_uint_small. smt ().
        have H9' : 128 <= to_uint dest{1}. smt (@W256 @Utils).
        have J0 : to_uint dest{1} < W256.modulus. apply uint256_size.
        rewrite mod_plus.
        rewrite mod_eq_self. smt (). smt. smt. smt.

        rewrite MemoryMap.load_store_diff.
    
        have J0 : dest{1} + (of_int 32)%W256 - (of_int 64)%W256 = dest{1} - (of_int 32)%W256. smt (@Utils @W256).
        rewrite J0.
        rewrite Utils.uint256_cast_sub.
        apply uint256_le_of_le.
        rewrite to_uint_small. smt ().
        rewrite to_uint_small. smt (@IntDiv @W256).
        have H9' : 128 <= to_uint dest{1}. smt (@W256 @Utils).
        have J1 : to_uint dest{1} < W256.modulus. apply uint256_size.
        rewrite mod_eq_self. smt (). smt (). smt. smt ().

        have K0 : (of_int 64)%W256 - (dest{1} + (of_int 32)%W256) = (W256.of_int 32) - dest{1}.
        rewrite uint256_distrib_sub. smt (@W256 @Utils).
        rewrite K0.
        rewrite Utils.uint256_cast_sub.
        apply uint256_le_of_le.
        rewrite to_uint_small. smt ().
        rewrite to_uint_small. smt ().
        have H9' : 128 <= to_uint dest{1}. smt (@W256 @Utils).
        have J0 : to_uint dest{1} < W256.modulus. apply uint256_size.
        rewrite mod_plus.
        rewrite mod_eq_self. smt (). smt. smt. smt.

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils).
        smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils).
        smt (@W256 @Utils).
    
    
        smt (@MemoryMap).
        elim*=> x y.

        case (ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int (FieldQ.asint x), W256.of_int (FieldQ.asint y)) (W256.of_int x2v, W256.of_int y2v)).

        seq 0 0 :
    (
      exists (x' y' : FieldQ.F),
      ((0 <= x1v && x1v < FieldQ.p) /\
        (0 <= y1v && y1v < FieldQ.p) /\
        (0 <= sv && sv < W256.modulus) /\
        (0 <= x2v && x2v < FieldQ.p) /\
        (0 <= y2v && y2v < FieldQ.p) /\
        x2_F{2} = FieldQ.inF x2v /\
        y2_F{2} = FieldQ.inF y2v /\
        (point{1}, s{1}, dest{1}) = (p1u, (of_int sv)%W256, destu) /\
        (x1{2}, y1{2}, s{2}, x2{2}, y2{2}) = (x1v, y1v, sv, x2v, y2v) /\
          !Primops.reverted{1} /\
        (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v)
          (W256.of_int sv)) /\
            ecMul_precompile (FieldQ.inF x1v) (FieldQ.inF y1v) sv =
            Some (x, y) /\
            ecAdd_precompile x y (FieldQ.inF x2v) (FieldQ.inF y2v) =
            Some (x', y') /\
        success{1} = W256.one /\
        mresult'{2} = (x, y) /\
            Primops.memory{1} =
        (PurePrimops.mstore
          ((PurePrimops.mstore
              ((PurePrimops.mstore
                  ((PurePrimops.mstore memory0 W256.zero
                      (W256.of_int (FieldQ.asint x))))
                  ((of_int 32))%W256 ((of_int ((FieldQ.asint y))))%W256))%PurePrimops
              ((of_int 64))%W256 ((of_int x2v))%W256))%PurePrimops
          ((of_int 96))%W256 ((of_int y2v))%W256)%PurePrimops) /\
      (ConcretePrimops.staticcall_ec_add_should_succeed
        ((of_int ((FieldQ.asint x)))%W256,
          (of_int ((FieldQ.asint y)))%W256)
        ((of_int x2v)%W256, (of_int y2v)%W256))
    ). skip. progress.
        have H13 := ConcretePrimops.ecAdd_precomp_is_some_of_should_succeed _ _ H12.
        simplify H13.
        rewrite proj1 proj1 proj2 proj2 in H13.
        rewrite to_uint_small in H13. smt.
        rewrite to_uint_small in H13. smt.
        rewrite to_uint_small in H13. smt.
        rewrite to_uint_small in H13. smt.
        rewrite FieldQ.asintK FieldQ.asintK in H13.
        have H14 := exists_of_is_some _ H13.
        case H14. progress.
        exists v.`1. exists v.`2. progress. smt ().

        elim*=> x' y'.
    
          seq 1 1 :
    (
        (0 <= x1v && x1v < FieldQ.p) /\
        (0 <= y1v && y1v < FieldQ.p) /\
        (0 <= sv && sv < W256.modulus) /\
        (0 <= x2v && x2v < FieldQ.p) /\
        (0 <= y2v && y2v < FieldQ.p) /\
        x2_F{2} = FieldQ.inF x2v /\
        y2_F{2} = FieldQ.inF y2v /\
        (point{1}, s{1}, dest{1}) = (p1u, (of_int sv)%W256, destu) /\
        (x1{2}, y1{2}, s{2}, x2{2}, y2{2}) = (x1v, y1v, sv, x2v, y2v) /\
          !Primops.reverted{1} /\
        (ConcretePrimops.staticcall_ec_mul_should_succeed ((of_int x1v)%W256, (of_int y1v)%W256)
          ((of_int sv))%W256) /\
        success{1} = W256.one /\
            ecMul_precompile ((FieldQ.inF x1v)) ((FieldQ.inF y1v)) sv = Some (x, y) /\
        mresult'{2} = (x, y) /\
        ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int (FieldQ.asint x), W256.of_int (FieldQ.asint y)) (W256.of_int x2v, W256.of_int y2v) /\
        _16{1} = W256.one /\
        ecAdd_precompile x y (FieldQ.inF x2v) (FieldQ.inF y2v) = Some (x', y') /\
        aresult{2} = Some (x', y') /\
        Primops.memory{1} =
            PurePrimops.mstore
            (PurePrimops.mstore 
            ((PurePrimops.mstore
              ((PurePrimops.mstore
                  ((PurePrimops.mstore
                      ((PurePrimops.mstore memory0 W256.zero
                          ((of_int ((FieldQ.asint x))))%W256))
                      ((of_int 32))%W256 ((of_int ((FieldQ.asint y))))%W256))
                  ((of_int 64))%W256 ((of_int x2v))%W256))
              ((of_int 96))%W256 ((of_int y2v))%W256)) destu (W256.of_int (FieldQ.asint x'))) (destu + W256.of_int 32) (W256.of_int (FieldQ.asint y'))
    ).
    
    
      
        exists* Primops.memory{1}.
        elim*=>memory2. progress.
      
        call {1} (ConcretePrimops.staticcall_ec_add_pspec memory2 (W256.of_int (FieldQ.asint x), W256.of_int (FieldQ.asint y)) (W256.of_int x2v, W256.of_int y2v) W256.zero destu).
    
        wp. skip. progress.
        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        smt (@MemoryMap).

        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        smt (@MemoryMap).

        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        smt (@MemoryMap).

        smt (@MemoryMap).

        smt ().

        have J0 :
    (
      memory_L =
      (PurePrimops.mstore
        ((PurePrimops.mstore
            ((PurePrimops.mstore
                ((PurePrimops.mstore
                    ((PurePrimops.mstore
                        ((PurePrimops.mstore memory0 W256.zero
                            ((W256.of_int (FieldQ.asint x)))))
                        ((W256.of_int 32))
                        ((W256.of_int ((FieldQ.asint y))))))%PurePrimops
                    ((of_int 64))%W256 ((of_int x2{2}))%W256))%PurePrimops
                ((of_int 96))%W256 ((of_int y2{2}))%W256))%PurePrimops
                  dest{1}
            ((ConcretePrimops.ecAdd_precompile_unsafe_cast
                ((of_int ((FieldQ.asint x)))%W256,
                  (of_int ((FieldQ.asint y)))%W256)
                ((of_int x2{2})%W256, (of_int y2{2})%W256))).`1))%PurePrimops
        (dest{1} + (of_int 32)%W256)
        ((ConcretePrimops.ecAdd_precompile_unsafe_cast
            ((W256.of_int ((FieldQ.asint x))),
              (W256.of_int ((FieldQ.asint y))))
            ((of_int x2{2})%W256, (of_int y2{2})%W256))).`2)%PurePrimops
    ). smt ().
        rewrite /ecAdd_precompile_unsafe_cast in J0.
        rewrite J0. progress.
        rewrite to_uint_small. smt.
        rewrite to_uint_small. smt.
        rewrite to_uint_small. smt.
        rewrite to_uint_small. smt.
        rewrite FieldQ.asintK FieldQ.asintK H12.
        rewrite odflt_some_eq proj1 proj2.
        reflexivity.
        seq 1 0 : (#pre). wp. skip. progress. rewrite PurePrimops.bit_andE. smt ().
        rcondf {1} 1. progress. skip. progress. smt (). wp. skip. progress.
        exists x. exists y. progress. exists x'. exists y'. progress.
        seq 1 1 : (_16{1} = W256.zero /\ success{1} = W256.one /\ aresult{2} = None /\ !ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int (FieldQ.asint x), W256.of_int (FieldQ.asint y)) (W256.of_int x2v, W256.of_int y2v) /\ ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv)).
        exists* Primops.memory{1}.
        elim* => memory1.

        call {1} (ConcretePrimops.staticcall_ec_add_pspec memory1 (W256.of_int (FieldQ.asint x), W256.of_int (FieldQ.asint y)) (W256.of_int x2v, W256.of_int y2v) W256.zero destu).
        wp. skip. progress.

        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        smt (@MemoryMap).

        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        smt (@MemoryMap).

        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        smt (@MemoryMap).

        smt (@MemoryMap).

        smt ().

        apply eq_none_of_is_none.
        have J0 := ConcretePrimops.ecAdd_precomp_is_none_of_should_not_succeed (W256.of_int (FieldQ.asint x), W256.of_int (FieldQ.asint y)) (W256.of_int x2{2}, W256.of_int y2{2}).
        rewrite proj1 proj1 proj2 proj2 in J0.
        rewrite to_uint_small in J0. smt.
        rewrite to_uint_small in J0. smt.
        rewrite to_uint_small in J0. smt.
        rewrite to_uint_small in J0. smt.
        rewrite FieldQ.asintK FieldQ.asintK in J0.
        apply J0.
        progress.
        smt (@FieldQ @EllipticCurve).
        smt (@FieldQ @EllipticCurve).

        seq 1 1 :
    (
      _16{1} = W256.zero /\
      success{1} = W256.zero /\
      fresult{2} = None /\
      ! (ConcretePrimops.staticcall_ec_add_should_succeed
        ((of_int ((FieldQ.asint x)))%W256,
          (of_int ((FieldQ.asint y)))%W256)
        ((of_int x2v)%W256, (of_int y2v)%W256)) /\
      (ConcretePrimops.staticcall_ec_mul_should_succeed ((of_int x1v)%W256, (of_int y1v)%W256)
        ((of_int sv))%W256)
    ).
        wp. skip. progress. rewrite PurePrimops.bit_andE. smt ().
        rcondt {1} 1. progress. skip. progress. smt (@W256).
        inline *. wp. skip. progress. left. progress. exists x. exists y. smt ().
        seq 1 1 : (success{1} = W256.zero /\ mresult{2} = None /\ !Primops.reverted{1} /\
        ! (ConcretePrimops.staticcall_ec_mul_should_succeed ((of_int x1v)%W256, (of_int y1v)%W256)
        ((of_int sv))%W256)).
          exists* Primops.memory{1}.
          elim*=>memory1. progress.

          call {1} (ConcretePrimops.staticcall_ec_mul_pspec memory1 (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) W256.zero W256.zero). wp. skip. progress. 
      
    
          rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
          smt (@MemoryMap).
    
          rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
          smt (@MemoryMap).
    
          smt (@MemoryMap).
    
          smt ().

          apply eq_none_of_is_none.

          have J0 := ConcretePrimops.ecMul_precomp_is_none_of_should_not_succeed (W256.of_int x1{2}, W256.of_int y1{2}) (W256.of_int s{2}).
          rewrite proj1 proj2 in J0.
          rewrite to_uint_small in J0. smt.
          rewrite to_uint_small in J0. smt.
          rewrite to_uint_small in J0. smt.
          apply J0. progress.
          rcondf {2} 1. progress.
          seq 7 1 :
    (
      success{1} = W256.zero /\
      fresult{2} = None /\
      !Primops.reverted{1} /\
      ! (ConcretePrimops.staticcall_ec_mul_should_succeed ((of_int x1v)%W256, (of_int y1v)%W256)
        ((of_int sv))%W256)
    ). inline *. wp. skip. progress.
        rewrite PurePrimops.bit_andE. smt ().
        rewrite PurePrimops.bit_andE. smt ().
        rewrite PurePrimops.bit_andE. smt ().
        rewrite PurePrimops.bit_andE. smt ().
        rewrite PurePrimops.bit_andE. smt ().
        rewrite PurePrimops.bit_andE. smt ().
        rcondt {1} 1. progress. skip. progress. smt (@W256 @PurePrimops).

        inline *. wp. skip. progress. right. exact H0.
    qed.
    
lemma PointMulAndAddIntoDest_low_equiv_mid_err : equiv [
    PointMulAndAddIntoDest.low ~ PointMulAndAddIntoDest.mid :
    Primops.reverted{1} ==> Primops.reverted{1}
    ]. proof.
        proc.
        inline mload mstore Primops.gas. wp. sp.
        seq 1 0 : Primops.reverted{1}.
        call{1} ConcretePrimops.staticcall_pspec_revert. skip. progress.
        sp.
        seq 1 0 : Primops.reverted{1}.
        call{1} ConcretePrimops.staticcall_pspec_revert. skip. progress.
        sp.
        case (bool_of_uint256 (PurePrimops.iszero success{1})).
        rcondt{1} 1. progress.
        inline*. wp. skip. progress.
        rcondf{1} 1. progress. skip. progress.
  qed.

  lemma pointMulAndAddIntoDest_mid_equiv_high_field:
  equiv [
      PointMulAndAddIntoDest.mid ~ PointMulAndAddIntoDest.high_field:
        x1{1} = (F_to_int_point p1{2}).`1 /\
        y1{1} = (F_to_int_point p1{2}).`2 /\
        x2{1} = (F_to_int_point p2{2}).`1 /\
        y2{1} = (F_to_int_point p2{2}).`2 /\
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
        have H_mul: exists (p_mul: FieldQ.F*FieldQ.F), ecMul_precompile p1{2}.`1 p1{2}.`2 (FieldR.asint s{2}) = Some p_mul by exact exists_of_is_some.
        case H_mul. move=> p_mul H_p_mul. rewrite H_p_mul. simplify.
        case (ecAdd_precompile p_mul.`1 p_mul.`2 p2{2}.`1 p2{2}.`2).
        by progress.
      move=>p_add. right.
        exists (F_to_int_point p_add). exists p_add. by progress.
        rewrite F_to_int_point_inzmod_1 in H0.
        rewrite F_to_int_point_inzmod_2 in H0.
        by progress.
        rewrite F_to_int_point_inzmod_1 in H0.
        rewrite F_to_int_point_inzmod_2 in H0.
        by progress.
      qed.
        
lemma pointMulAndAddIntoDest_high_field_equiv_high:
equiv [
    PointMulAndAddIntoDest.high_field ~ PointMulAndAddIntoDest.high:
      aspoint_G1 p1{2} = p1{1} /\
      aspoint_G1 p2{2} = p2{1} /\
      s{1} = s{2} ==>
      res{1} = Some (aspoint_G1 res{2})
    ].
    proof.
      proc.
      wp.
      skip.
      progress.
      by rewrite - (ecMul_def (aspoint_G1 p1{2}).`1 (aspoint_G1 p1{2}).`2 (FieldR.asint s{2}) p1{2}); [ smt () | progress ].
      case (exists_of_is_some _ H). move => p_mul H_mul. rewrite H_mul. simplify.
      rewrite (ecAdd_def p_mul.`1 p_mul.`2 (aspoint_G1 p2{2}).`1 (aspoint_G1 p2{2}).`2 (s{2} * p1{2}) p2{2}).
      have ->: (aspoint_G1 (s{2} * p1{2}) = (p_mul.`1, p_mul.`2)) = (Some (aspoint_G1 (FieldR.inF (FieldR.asint s{2}) * p1{2})) = Some (p_mul)). rewrite FieldR.asintK. smt ().
      rewrite -H_mul. apply ecMul_def; smt ().
      smt ().
      reflexivity.
  qed.

lemma pointMulAndAddIntoDest_mid_equiv_high:
equiv [
    PointMulAndAddIntoDest.mid ~ PointMulAndAddIntoDest.high:
      x1{1} = (F_to_int_point (aspoint_G1 p1{2})).`1 /\
      y1{1} = (F_to_int_point (aspoint_G1 p1{2})).`2 /\    
      x2{1} = (F_to_int_point (aspoint_G1 p2{2})).`1 /\
      y2{1} = (F_to_int_point (aspoint_G1 p2{2})).`2 /\
      s{1} = FieldR.asint s{2} ==>
      res{1} = Some (F_to_int_point (aspoint_G1 res{2}))
    ].
    proof.
      transitivity PointMulAndAddIntoDest.high_field
    (
      x1{1} = (F_to_int_point p1{2}).`1 /\
      y1{1} = (F_to_int_point p1{2}).`2 /\
      x2{1} = (F_to_int_point p2{2}).`1 /\
      y2{1} = (F_to_int_point p2{2}).`2 /\
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
      aspoint_G1 p1{2} = p1{1} /\
      aspoint_G1 p2{2} = p2{1} /\
      s{1} = s{2} ==>
      res{1} = Some (aspoint_G1 res{2})
    ).
        by progress; exists (aspoint_G1 p1{2}, s{2}, aspoint_G1 p2{2}); progress.
        by progress; case H; progress.
        exact pointMulAndAddIntoDest_mid_equiv_high_field.
        exact pointMulAndAddIntoDest_high_field_equiv_high.
    qed.    
      
