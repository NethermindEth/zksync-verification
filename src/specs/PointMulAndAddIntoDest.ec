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
      x1_F <- ZModField.inzmod x1;
      y1_F <- ZModField.inzmod y1;
      mresult <- ecMul_precompile x1_F y1_F s;
      if (is_some mresult) {
         x2_F <- ZModField.inzmod x2;
         y2_F <- ZModField.inzmod y2;
         mresult' <- odflt (ZModField.zero, ZModField.zero) mresult;
         aresult  <- ecAdd_precompile mresult'.`1 mresult'.`2 x2_F y2_F; 
         fresult <- omap F_to_uint256_point aresult;
      } else {
          fresult <- None;
      }
      return fresult;
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


lemma small_neg_mono (a b c : uint256) : a <= b => c <= a => a - c <= b - c.
    progress.
    rewrite uint_256_cast_sub uint_256_cast_sub.
    apply uint256_le_of_le.
    rewrite to_uint_small. smt ().
    rewrite to_uint_small. smt ().
    have H'  := uint256_le_of_le' _ _ H.
    have H0' := uint256_le_of_le' _ _ H0.
    pose av := W256.to_uint a.
    pose bv := W256.to_uint b.
    pose cv := W256.to_uint c.
    have H1' : cv <= bv. smt ().
    have HA : av < W256.modulus. exact (uint256_size _).
    have HB : bv < W256.modulus. exact (uint256_size _).
    have HC : cv < W256.modulus. exact (uint256_size _).
    have HA' : 0 <= av. smt (@W256).
    have HB' : 0 <= bv. smt (@W256).
    have HC' : 0 <= cv. smt (@W256).
    rewrite mod_eq_self. smt (). smt ().
    have INT : av - cv <= av. smt ().
    smt.
    rewrite mod_eq_self. smt (). smt ().
    have INT : bv - cv <= bv. smt ().
    smt.
    smt ().
  qed.

lemma PointMulAndAddIntoDest_mid_of_low (x1v y1v x2v y2v sv : int) (p1u destu : uint256) (memory0 : MemoryMap.mem) : equiv [
    PointMulAndAddIntoDest.low ~ PointMulAndAddIntoDest.mid :
    Primops.memory{1} = memory0 /\
      0 <= x1v < p /\ 0 <= y1v < p /\ 0 <= sv < W256.modulus /\ 0 <= x2v < p /\ 0 <= y2v < p /\
      (of_int 128)%W256 < p1u /\
      (of_int 128)%W256 < -p1u /\
      (of_int 128)%W256 < p1u + (of_int 32)%W256 /\
      (of_int 128)%W256 < - (p1u + (of_int 32)%W256) /\
      (of_int 128)%W256 < destu /\
      (of_int 128)%W256 < -destu /\
      (of_int 128)%W256 < destu + (of_int 32)%W256 /\
      (of_int 128)%W256 < - (destu + (of_int 32)%W256) /\
    PurePrimops.mload memory0 p1u = W256.of_int x1v /\
    PurePrimops.mload memory0 (p1u + W256.of_int 32) = W256.of_int y1v /\
    PurePrimops.mload memory0 destu = W256.of_int x2v /\
    PurePrimops.mload memory0 (destu + W256.of_int 32) = W256.of_int y2v /\
      arg{1} = (p1u, W256.of_int sv, destu) /\ arg{2} = (x1v, y1v, sv, x2v, y2v) /\ !Primops.reverted{1}
      ==>
      (
        ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) /\
        exists (x y : F),
        ecMul_precompile (ZModField.inzmod x1v) (ZModField.inzmod y1v) sv = Some (x, y) /\
        (
          ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int (ZModField.asint x), W256.of_int (ZModField.asint y)) (W256.of_int x2v, W256.of_int y2v) /\
          exists (x' y' : F),
          ecAdd_precompile x y (ZModField.inzmod x2v) (ZModField.inzmod y2v) = Some (x', y') /\
          Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero (W256.of_int (ZModField.asint x))) (W256.of_int 32) (W256.of_int (ZModField.asint y))) (W256.of_int 64) (W256.of_int x2v)) (W256.of_int 96) (W256.of_int y2v)) destu (W256.of_int (ZModField.asint x'))) (destu + W256.of_int 32) (W256.of_int (ZModField.asint y')) /\ 
          !Primops.reverted{1}
        )
        \/
        (
          !ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int (ZModField.asint x), W256.of_int (ZModField.asint y)) (W256.of_int x2v, W256.of_int y2v) /\
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
      0 <= x1v < p /\ 0 <= y1v < p /\ 0 <= sv < W256.modulus /\ 0 <= x2v < p /\ 0 <= y2v < p /\
      (of_int 128)%W256 < destu /\
      (of_int 128)%W256 < -destu /\
      (of_int 128)%W256 < destu + (of_int 32)%W256 /\
      (of_int 128)%W256 < - (destu + (of_int 32)%W256) /\
      PurePrimops.mload memory0 destu = W256.of_int x2v /\
      PurePrimops.mload memory0 (destu + W256.of_int 32) = W256.of_int y2v /\
      Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero (W256.of_int x1v)) (W256.of_int 32) (W256.of_int y1v)) (W256.of_int 64) (W256.of_int sv) /\
      x1_F{2} = ZModField.inzmod x1v /\ y1_F{2} = ZModField.inzmod y1v /\
      (point{1}, s{1}, dest{1}) = (p1u, W256.of_int sv, destu) /\ (x1{2}, y1{2}, s{2}, x2{2}, y2{2}) = (x1v, y1v, sv, x2v, y2v) /\ !Primops.reverted{1}
    ).
        inline *. wp. skip. progress. congr.

        rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
        rewrite H17 H18. reflexivity.

        case (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv)).

        seq 1 1 :
    (
      (0 <= x1v && x1v < p) /\
      (0 <= y1v && y1v < p) /\
      (0 <= sv && sv < W256.modulus) /\
      (0 <= x2v && x2v < p) /\
      (0 <= y2v && y2v < p) /\
        W256.of_int 128 < destu /\
        W256.of_int 128 < -destu /\
        W256.of_int 128 < destu + (W256.of_int 32) /\
        W256.of_int 128 < - (destu + (W256.of_int 32)) /\
        PurePrimops.mload memory0 destu = W256.of_int x2v /\
        PurePrimops.mload memory0 (destu + (W256.of_int 32)) = W256.of_int y2v /\
      x1_F{2} = ZModField.inzmod x1v /\
      y1_F{2} = ZModField.inzmod y1v /\
        (point{1}, s{1}, dest{1}) = (p1u, W256.of_int sv, destu) /\
        (x1{2}, y1{2}, s{2}, x2{2}, y2{2}) = (x1v, y1v, sv, x2v, y2v) /\
          !Primops.reverted{1} /\
        (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v)
          (W256.of_int sv)) /\
            exists (x y : F),
        ecMul_precompile x1_F{2} y1_F{2} sv = Some (x, y) /\
        success{1} = W256.one /\ mresult{2} = Some (x, y) /\
            Primops.memory{1} =
        (PurePrimops.mstore
          ((PurePrimops.mstore ((PurePrimops.mstore memory0 W256.zero ((W256.of_int (ZModField.asint x)))))
              (W256.of_int 32) (W256.of_int (ZModField.asint y))))
          (W256.of_int 64) (W256.of_int sv))
      ).

          exists* Primops.memory{1}.
          elim*=> memory1.
          call {1} (ConcretePrimops.staticcall_ec_mul_pspec memory1 (W256.of_int x1v, W256.of_int y1v) (W256.of_int sv) W256.zero W256.zero). wp. skip. progress. 

          rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite MemoryMap.load_store_same. reflexivity.

          rewrite MemoryMap.load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
          rewrite MemoryMap.load_store_same. reflexivity.

          rewrite MemoryMap.load_store_same. reflexivity.

          have J0 := exists_of_is_some _ (ConcretePrimops.ecMul_precomp_is_some_of_should_succeed _ _ H16).
          case J0. move=>pt J0. pose x := pt.`1. pose y := pt.`2. exists x. exists y.
      have J0' : ecMul_precompile
      (ZModField.inzmod (to_uint (W256.of_int x1{2})))
      (ZModField.inzmod (to_uint (W256.of_int y1{2})))
      (to_uint (W256.of_int s{2})) =
        Some pt. smt ().
        rewrite to_uint_small in J0'. progress. apply (lt_trans _ p _). exact H0. exact p_lt_W256_mod.
        rewrite to_uint_small in J0'. progress. apply (lt_trans _ p _). exact H2. exact p_lt_W256_mod.
        rewrite to_uint_small in J0'. smt ().
        progress. smt (). smt (). smt ().

        have J1 : memory_L =
      (PurePrimops.mstore
        ((PurePrimops.mstore
            ((PurePrimops.mstore
                ((PurePrimops.mstore
                    ((PurePrimops.mstore memory0 W256.zero ((of_int x1{2}))%W256))%PurePrimops
                    ((of_int 32))%W256 ((of_int y1{2}))%W256))%PurePrimops
                ((of_int 64))%W256 ((of_int s{2}))%W256))%PurePrimops
                  W256.zero
            ((ConcretePrimops.ecMul_precompile_unsafe_cast
                ((of_int x1{2})%W256, (of_int y1{2})%W256)
                ((of_int s{2}))%W256))%ConcretePrimops.`1))%PurePrimops
        ((of_int 32))%W256
        ((ConcretePrimops.ecMul_precompile_unsafe_cast
            ((of_int x1{2})%W256, (of_int y1{2})%W256) ((of_int s{2}))%W256)).`2). smt ().
              rewrite J1.
              rewrite -(MemoryMap.store_store_swap_diff _ W256.zero). smt (@W256 @Utils). smt (@W256 @Utils).
              rewrite -(MemoryMap.store_store_swap_diff _ W256.zero). smt (@W256 @Utils). smt (@W256 @Utils).
              rewrite MemoryMap.store_store_same.

              rewrite -(MemoryMap.store_store_swap_diff _ (W256.of_int 32)). smt (@W256 @Utils). smt (@W256 @Utils).
              rewrite MemoryMap.store_store_same. 
              rewrite /ecMul_precompile_unsafe_cast. simplify.
              rewrite to_uint_small. progress. apply (lt_trans _ p _). exact H0. exact p_lt_W256_mod.
              rewrite to_uint_small. progress. apply (lt_trans _ p _). exact H2. exact p_lt_W256_mod.
              rewrite to_uint_small. progress.

              rewrite J0'.
              congr. smt ().
              rcondt {2} 1. progress.

              seq 5 3 :
      (
        (0 <= x1v && x1v < p) /\
        (0 <= y1v && y1v < p) /\
        (0 <= sv && sv < W256.modulus) /\
        (0 <= x2v && x2v < p) /\
        (0 <= y2v && y2v < p) /\
        x2_F{2} = ZModField.inzmod x2v /\
        y2_F{2} = ZModField.inzmod y2v /\
        (point{1}, s{1}, dest{1}) = (p1u, W256.of_int sv, destu) /\
        (x1{2}, y1{2}, s{2}, x2{2}, y2{2}) = (x1v, y1v, sv, x2v, y2v) /\
          !Primops.reverted{1} /\
        (ConcretePrimops.staticcall_ec_mul_should_succeed (W256.of_int x1v, W256.of_int y1v)
          (W256.of_int sv)) /\
            exists (x y : F),
        ecMul_precompile (ZModField.inzmod x1v) (ZModField.inzmod y1v) sv = Some (x, y) /\
        success{1} = W256.one /\
        mresult'{2} = (x, y) /\
            Primops.memory{1} =
        PurePrimops.mstore (PurePrimops.mstore
          (PurePrimops.mstore
              (PurePrimops.mstore memory0 W256.zero (W256.of_int (ZModField.asint x)))
              (W256.of_int 32) (W256.of_int (ZModField.asint y)))
          (W256.of_int 64) (W256.of_int x2v)) (W256.of_int 96) (W256.of_int y2v)
      ).

          inline *. wp. skip. progress.
          exists x. exists y.
          progress.

      
          rewrite MemoryMap.load_store_diff.
          admit. admit.
          rewrite MemoryMap.load_store_diff.
          admit. admit.
          rewrite MemoryMap.load_store_diff.
          admit. admit.
          rewrite MemoryMap.load_store_diff.
          admit. admit.
          rewrite MemoryMap.load_store_diff.
          admit. admit.
          rewrite MemoryMap.load_store_diff.
          admit. admit.
          rewrite MemoryMap.load_store_diff.
          admit. admit.
          smt (@MemoryMap).

          seq 1 1 :
      (
        (0 <= x1v && x1v < p) /\
        (0 <= y1v && y1v < p) /\
        (0 <= sv && sv < W256.modulus) /\
        (0 <= x2v && x2v < p) /\
        (0 <= y2v && y2v < p) /\
        x2_F{2} = ZModField.inzmod x2v /\
        y2_F{2} = ZModField.inzmod y2v /\
        (point{1}, s{1}, dest{1}) = (p1u, (of_int sv)%W256, destu) /\
        (x1{2}, y1{2}, s{2}, x2{2}, y2{2}) = (x1v, y1v, sv, x2v, y2v) /\
          !Primops.reverted{1} /\
        (ConcretePrimops.staticcall_ec_mul_should_succeed ((of_int x1v)%W256, (of_int y1v)%W256)
          ((of_int sv))%W256) /\
        success{1} = W256.one /\
            exists (x y : F),
            ecMul_precompile ((ZModField.inzmod x1v)) ((ZModField.inzmod y1v)) sv = Some (x, y) /\
        mresult'{2} = (x, y) /\
        (
          (
            ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int (ZModField.asint x), W256.of_int (ZModField.asint y)) (W256.of_int x2v, W256.of_int y2v) /\
            _16{1} = W256.one /\
            exists (x' y' : F),
            ecAdd_precompile x y (ZModField.inzmod x2v) (ZModField.inzmod y2v) = Some (x', y') /\
            aresult{2} = Some (x', y') /\
            Primops.memory{1} =
            PurePrimops.mstore
            (PurePrimops.mstore 
            ((PurePrimops.mstore
              ((PurePrimops.mstore
                  ((PurePrimops.mstore
                      ((PurePrimops.mstore memory0 W256.zero
                          ((of_int ((ZModField.asint x))))%W256))
                      ((of_int 32))%W256 ((of_int ((ZModField.asint y))))%W256))
                  ((of_int 64))%W256 ((of_int x2v))%W256))
              ((of_int 96))%W256 ((of_int y2v))%W256)) destu (W256.of_int (ZModField.asint x'))) (destu + W256.of_int 32) (W256.of_int (ZModField.asint y'))
          )
              \/
          (
            ! (ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int (ZModField.asint x), W256.of_int (ZModField.asint y)) (W256.of_int x2v, W256.of_int y2v)) /\
            _16{1} = W256.zero /\
            aresult{2} = None /\
            Primops.memory{1} =
            (PurePrimops.mstore
              ((PurePrimops.mstore
                  ((PurePrimops.mstore
                      ((PurePrimops.mstore memory0 W256.zero
                          ((of_int ((ZModField.asint x))%ZModField))%W256))%PurePrimops
                      ((of_int 32))%W256 ((of_int ((ZModField.asint y))))%W256))%PurePrimops
                  ((of_int 64))%W256 ((of_int x2v))%W256))%PurePrimops
              ((of_int 96))%W256 ((of_int y2v))%W256)%PurePrimops
          )
      )
    ).
    
    
      
          exists* Primops.memory{1}.
          elim*=>memory2. progress.
      
        call {1} (ConcretePrimops.staticcall_ec_add_pspec memory2 (W256.of_int (ZModField.asint x), W256.of_int (ZModField.asint y)) (W256.of_int x2v, W256.of_int y2v) W256.zero destu).
    
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

        exists x. exists y.
        progress.
    
        case (ConcretePrimops.staticcall_ec_add_should_succeed
      ((W256.of_int (ZModField.asint x)),
        (W256.of_int (ZModField.asint y)))
      ((W256.of_int x2{2}), (W256.of_int y2{2}))).
        progress. smt ().

        have J0 := exists_of_is_some _ (ConcretePrimops.ecAdd_precomp_is_some_of_should_succeed _ _ H18).
        case J0. move=>pt' J0. pose x' := pt'.`1. pose y' := pt'.`2. exists x'. exists y'. progress.

        have J0' : ecAdd_precompile
    ((ZModField.inzmod
        (to_uint
          ((W256.of_int ((ZModField.asint x)))))))
    ((ZModField.inzmod
        (W256.to_uint
          ((of_int ((ZModField.asint y))%ZModField)%W256))))%ZModField
    ((ZModField.inzmod (to_uint ((of_int x2{2})%W256))))%ZModField
    ((ZModField.inzmod (to_uint ((of_int y2{2})%W256))))%ZModField =
      Some pt'. smt ().
      rewrite to_uint_small in J0'. admit.
      rewrite to_uint_small in J0'. admit.
      rewrite to_uint_small in J0'. admit.
      rewrite to_uint_small in J0'. admit.
      smt (@ZModField).

      admit.

      smt (@MemoryMap).

      progress. smt (). admit.

      smt ().

      inline *. progress.

      seq 1 0 : (#pre /\ success{1} = _16{1}).
      admit.
      inline *. wp. skip. progress. left. progress. exists x'.

    
    
    
        rewrite to_uintK in J0.

    
    
    
          case (ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int (ZModField.asint x)) (W256.of_int (ZModField.asint y)) (W256.of_int x2v) (W256.of_int y2v)).

      
          reflexivity.
          smt (@W256 @Utils).
      

      
        smt (@MemoryMap @W256 @Utils).
