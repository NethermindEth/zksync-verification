pragma Goals:printall.

require import AllCore.
require import Array.
require import Int.
require import IntDiv.
require import Real.
require import UInt256.
require import YulPrimops.
require import PurePrimops.
require import Utils.
require import JUtils.

module Test = {
  proc writeReadTest(address: uint256, value: uint256): uint256 = {
      var _1;
      Primops.mstore(address, value);
      _1 <@ Primops.mload(address);
      return _1;
    }

    proc revert_if_two(x : uint256) : uint256 = {
        var y;
        y <- x + (W256.of_int 3);
        if (bool_of_uint256 (PurePrimops.eq_uint256 y (W256.of_int 5))) {
        Primops.revert(W256.zero, W256.zero);
      }
      return y;
    }

    proc shifty(x : uint256, s : uint256) : uint256 = {
      var v1, v1', v2, v2' : uint256;
      if (bool_of_uint256 (PurePrimops.gt_uint256 s (W256.of_int 256))) {
        Primops.revert(W256.zero, W256.zero);
      }
      
      v1 <- PurePrimops.shl x s;
      v2 <- PurePrimops.shr x ((W256.of_int 256) - s);
      v1' <- PurePrimops.shr v1 s;
      v2' <- PurePrimops.shl v2 ((W256.of_int 256) - s);
      return (v1' + v2');
    }

    proc mod_test(m : uint256) : uint256 = {
        var mv, o, z : uint256;
        mv <- m - (W256.of_int 1);
        o <- PurePrimops.mulmod mv mv m;
        z <- PurePrimops.addmod o mv m;
        return z;
    }

    proc mstore8test(x: uint256, y: uint256): uint256 = {
      var x', z, z';
      Primops.mstore(W256.zero, W256.zero);
      Primops.mstore8(W256.zero, x);
      Primops.mstore8(W256.one, y);
      z <@ Primops.mload(W256.zero);
      x' <- PurePrimops.shl x (W256.of_int 248);
      z' <- PurePrimops.bit_and z x';
      return z;
    }

<<<<<<< HEAD
    proc calldata_test(ind : uint256) : uint256 = {
        var v1, v2, r : uint256;
        v1 <@ Primops.calldataload(ind);
        v2 <@ Primops.calldataload(ind);
        r <- PurePrimops.eq_uint256 v1 v2;
        return r;
    }
    
=======
    proc modexp_test(x: uint256, y: uint256, z: uint256) = {
        var success, ret;
        Primops.mstore(W256.zero, W256.of_int 32);
        Primops.mstore(W256.of_int 32, W256.of_int 32);
        Primops.mstore(W256.of_int 64, W256.of_int 32);
        Primops.mstore(W256.of_int 96, x); 
        Primops.mstore(W256.of_int 128, y);
        Primops.mstore(W256.of_int 160, z);
        success <@ Primops.staticcall(W256.one, W256.of_int 5, W256.zero, W256.of_int 192, W256.zero, W256.of_int 32);
        ret <@ Primops.mload(W256.zero);
        return (success, ret);
    }
>>>>>>> 1c08c2eeb00886bc62e2d0af99228e41e29d3394
  }.

lemma writeReadTest_correctness :

    forall (address value: uint256),
phoare [ Test.writeReadTest :
      arg = (address, value) ==>
      res = value] = 1%r.
proof.
    progress.
  proc.
  exists* Primops.memory.
  elim*=>memory_pre.
  call (ConcretePrimops.mload_pspec (PurePrimops.mstore memory_pre address value) address).
  call (ConcretePrimops.mstore_pspec memory_pre address value).
  skip.
  progress.
  apply PurePrimops.mload_mstore_same.
qed.
  
lemma revert_if_two_correctness (x : uint256) :
    phoare [Test.revert_if_two : arg = x /\ !Primops.reverted ==>
      (res = x + (W256.of_int 3)/\ x <> (W256.of_int 2) /\ !Primops.reverted) \/ (x = (W256.of_int 2) /\ Primops.reverted)] = 1%r.
        proc.
        inline Primops.revert.
        wp.
        skip.
        progress.
        rewrite /bool_of_uint256 /eq_uint256 in H0.
        have H1 : x{hr} + (of_int 3)%W256 = (of_int 5)%W256. smt ().
        rewrite (eq_sub_of_add_eq _ _ _ H1).
        progress.
        left.
        rewrite /bool_of_uint256 /eq_uint256 in H0.
        have H1 : x{hr} + (of_int 3)%W256 <> (of_int 5)%W256. smt (@W256).
        have H2 := neq_sub_of_add_neq _ _ _ H1.
        progress.
  qed.

lemma shifty_correctness (x s : uint256) :
    phoare [Test.shifty : arg = (x, s) /\ !Primops.reverted ==>
      (res = x /\ !Primops.reverted) \/ ((W256.of_int 256) < s /\ Primops.reverted)] = 1%r.
        proc.
        case ((W256.of_int 256) < s).
        rcondt 1.
        skip. progress.
        rewrite /bool_of_uint256 /gt_uint256. by smt (@W256).
        inline Primops.revert.
        wp.
        skip.
        by progress.
        rcondf 1.
        skip. progress.
        rewrite /bool_of_uint256 /gt_uint256. by smt (@W256).
        wp. skip. progress. 
        left.
        split; first last.
        exact H.
        rewrite /shr /shl.
        pose sh := to_uint s{hr}.
        pose sh' := to_uint ((W256.of_int 256) - s{hr}).
        rewrite W256.shrl_andmaskN. smt (@W256).
    case (to_uint s{hr} = 256).
        progress.
        rewrite /sh H1.
        pose v := x{hr}.
        have H2 : v `<<<` 256 = W256.zero. smt (@W256).
        have H3 : forall (s : int), W256.zero `>>>` s = W256.zero. progress. smt (@W256).
        have H4 : sh' = 0. smt (@W256).
        rewrite H2 H3 H4. simplify.
        smt (@W256).
        progress.
        rewrite W256.shlw_shrw_shlw. rewrite /sh.
        have H5 := (W256.to_uint_cmp s{hr}).
        simplify. progress.
        smt ().
        smt (@W256).
        simplify.
        rewrite shl_zero.
        have H6 : sh' = 256 - sh. smt.
        rewrite -H6.
        have H7 : x{hr} `&` (W256.masklsb sh') = (splitMask (W256.masklsb sh') x{hr}).`1. smt ().
        have H8 : x{hr} `&` (W256.invw (W256.masklsb sh')) = (splitMask (W256.masklsb sh') x{hr}).`2. smt ().
        rewrite H7 H8.
        exact W256.splitMask_add.
  qed.  
  
lemma mod_test_correctness (m : uint256) :
    phoare [Test.mod_test : arg = m /\ W256.one < m ==> res = W256.zero] = 1%r.
    proc.
    wp.
    skip.
    rewrite /PurePrimops.mulmod /PurePrimops.addmod.
    progress.
    have H0 : to_uint (m{hr} - W256.one) = (to_uint m{hr}) - 1. rewrite W256.to_uintB. smt (@W256). smt (@W256).
    rewrite H0.
    pose modu := to_uint m{hr}.
    have H1 : (modu - 1) * (modu - 1) = modu * (modu - 2) + 1. smt ().
    have H2 : (modu * (modu - 2) + 1) %% modu = 1. rewrite mul_add_mod_eq /modu. smt (@W256). smt (@W256).
    rewrite H1 H2.
    simplify.
    smt (@W256).
  qed.
  
lemma keccak_correctness (addr1 addr2 sz : uint256) : equiv [Primops.keccak256 ~ Primops.keccak256 : arg{1} = (addr1, sz) /\ arg{2} = (addr2, sz) /\ forall (i : uint256), W256.zero <= i /\ i < sz => Primops.memory{1}.[addr1 + i] = Primops.memory{2}.[addr2 + i] ==> res{1} = res{2}].
    proc.
    while (
      i{1} = i{2} /\
      i{1} <= sz /\
      size{1} = sz /\
      size{2} = sz /\
    Array.size input{1} = W256.to_uint sz /\
    Array.size input{2} = W256.to_uint sz /\
      forall (j : uint256),
        j < i{1} => (
          input{1}.[W256.to_uint j] = Primops.memory{1}.[off{1} + j] /\
          input{2}.[W256.to_uint j] = Primops.memory{2}.[off{2} + j]
      )
    ); first last.
        (* before the while *)
        wp. skip. progress.
        smt(@W256).
        rewrite Array.size_mkarray List.size_nseq. smt(@W256).
        rewrite Array.size_mkarray List.size_nseq. smt(@W256).
        smt (@W256).
        smt (@W256).
        congr.
        have H_i_R : i_R = size{1}. smt (@W256).
        progress.
        apply Array.eq_from_get. smt().
        progress.
        have H5_i0: W256.of_int i0 < i_R =>
          input_L.[to_uint (W256.of_int i0)] = Primops.memory{1}.[off{1} + W256.of_int i0] /\
        input_R.[to_uint (W256.of_int i0)] = Primops.memory{2}.[off{2} + W256.of_int i0].
        exact (H5 (W256.of_int i0)).
        rewrite H in H5_i0. smt (@W256).
        smt (@W256).
        (* inside the while *)
        wp. skip. progress. smt (@W256).
        smt (@Array @W256).
        smt (@Array @W256).
        smt (@Array @W256).
        smt (@Array @W256).
qed.

lemma splitMask_zero mask: W256.splitMask mask W256.zero = (W256.zero, W256.zero).
    proof.
      by smt(@W256).
  qed.

lemma zero_shl s: W256.zero `<<<` s = W256.zero.
    proof.
      by smt(@W256).
    qed.

lemma zero_shr s: W256.zero `>>>` s = W256.zero.
    proof.
      by smt(@W256).
    qed.

    hint simplify splitMask_zero, zero_shl, zero_shr.

  lemma neq_zero (i: int): 1 < i /\ i < 32 => W256.of_int i <> W256.zero.
      proof.
        admit.
    qed.
  lemma neq_one (i: int): 1 < i /\ i < 32 => W256.of_int i <> W256.one.
      proof.
        admit.
    qed.
  lemma byte_mask_id (a: uint256): a < W256.of_int 256 => a `&` (W256.masklsb 8) = a.
      proof.
        admit.
    qed.

  lemma add_shl (a b : uint256) (i: int): 0 <= i => (a + b) `<<<` i = (a `<<<` i) + (b `<<<` i).
      proof.
        progress.
        admit.
      qed.

lemma mstore8_test_correctness (a b: uint256): hoare[
    Test.mstore8test :
      arg = (a,b) /\ a < W256.of_int 256 /\ b < W256.of_int 256 ==> res = ((a `<<<` 8) + b) `<<<` 240
    ].
    proof.
      proc.
      seq 1 : (#pre /\ (forall (i: int), (0 <= i /\ i < 32) => Primops.memory.[W256.of_int i] = W256.zero)).
      inline Primops.mstore. wp. skip. progress.
    case (i = 0). progress. smt (@W256 @Map).
    case (i = 1). progress. smt (@W256 @Map).
    case (i = 2). progress. smt (@W256 @Map).
    case (i = 3). progress. smt (@W256 @Map).
    case (i = 4). progress. smt (@W256 @Map).
    case (i = 5). progress. smt (@W256 @Map).
    case (i = 6). progress. smt (@W256 @Map).
    case (i = 7). progress. smt (@W256 @Map).
    case (i = 8). progress. smt (@W256 @Map).
    case (i = 9). progress. smt (@W256 @Map).
    case (i = 10). progress. smt (@W256 @Map).
    case (i = 11). progress. smt (@W256 @Map).
    case (i = 12). progress. smt (@W256 @Map).
    case (i = 13). progress. smt (@W256 @Map).
    case (i = 14). progress. smt (@W256 @Map).
    case (i = 15). progress. smt (@W256 @Map).
    case (i = 16). progress. smt (@W256 @Map).
    case (i = 17). progress. smt (@W256 @Map).
    case (i = 18). progress. smt (@W256 @Map).
    case (i = 19). progress. smt (@W256 @Map).
    case (i = 20). progress. smt (@W256 @Map).
    case (i = 21). progress. smt (@W256 @Map).
    case (i = 22). progress. smt (@W256 @Map).
    case (i = 23). progress. smt (@W256 @Map).
    case (i = 24). progress. smt (@W256 @Map).
    case (i = 25). progress. smt (@W256 @Map).
    case (i = 26). progress. smt (@W256 @Map).
    case (i = 27). progress. smt (@W256 @Map).
    case (i = 28). progress. smt (@W256 @Map).
    case (i = 29). progress. smt (@W256 @Map).
    case (i = 30). progress. smt (@W256 @Map).
    case (i = 31). progress. smt (@W256 @Map).
    progress. smt (@W256).
      inline Primops.mstore8 Primops.mload. wp. skip. progress.
      do 30! (((rewrite Map.get_set_neqE; first exact neq_one);
      rewrite Map.get_set_neqE; first exact neq_zero);
      simplify);
    (rewrite H1; first trivial).
      do 29! (rewrite H1; first trivial).
      simplify.
      rewrite Map.get_set_sameE.
      rewrite Map.get_set_neqE. by smt(@W256).
      rewrite Map.get_set_sameE.
      rewrite byte_mask_id. exact H0.
      rewrite byte_mask_id. exact H.
      pose x' := to_uint x{hr}.
      pose y' := to_uint y{hr}.
      have H_x: x{hr} = W256.of_int x'. by smt(@W256).
      have H_y: y{hr} = W256.of_int y'. by smt (@W256).
      rewrite add_shl. trivial.
      rewrite W256.shlw_add. trivial. trivial. simplify. exact addrC.
  qed.

lemma modexp_test_correctness (a b c: uint256): hoare [ Test.modexp_test: arg = (a, b, c) ==> res = (W256.one, (
    W256.of_int (
            ((W256.to_uint a) ^ (W256.to_uint b)) %% (W256.to_uint c)
    )
  ))].
      proc.
      exists* Primops.memory.
      elim*. progress.
      pose mem_1 := PurePrimops.mstore memory W256.zero (W256.of_int 32).
      pose mem_2 := PurePrimops.mstore mem_1 (W256.of_int 32) (W256.of_int 32).
      pose mem_3 := PurePrimops.mstore mem_2 (W256.of_int 64) (W256.of_int 32).
      pose mem_4 := PurePrimops.mstore mem_3 (W256.of_int 96) a.
      pose mem_5 := PurePrimops.mstore mem_4 (W256.of_int 128) b.
      pose mem_6 := PurePrimops.mstore mem_5 (W256.of_int 160) c.
      have H_mem6_get0: PurePrimops.mload mem_6 W256.zero = W256.of_int 32.
      do 5! ((rewrite PurePrimops.apply_mstore_mload_diff; first smt(@W256)); first smt(@W256)).
      rewrite PurePrimops.mload_mstore_same. reflexivity.
      have H_mem6_get32: PurePrimops.mload mem_6 (W256.of_int 32) = W256.of_int 32.
      do 4! ((rewrite PurePrimops.apply_mstore_mload_diff; first smt(@W256)); first smt(@W256)).
      rewrite PurePrimops.mload_mstore_same. reflexivity.
      have H_mem6_get64: PurePrimops.mload mem_6 (W256.of_int 64) = W256.of_int 32.
      do 3! ((rewrite PurePrimops.apply_mstore_mload_diff; first smt(@W256)); first smt(@W256)).
      rewrite PurePrimops.mload_mstore_same. reflexivity.
      have H_mem6_get96: PurePrimops.mload mem_6 (W256.of_int 96) = a.
      do 2! ((rewrite PurePrimops.apply_mstore_mload_diff; first smt(@W256)); first smt(@W256)).
      rewrite PurePrimops.mload_mstore_same. reflexivity.
      have H_mem6_get128: PurePrimops.mload mem_6 (W256.of_int 128) = b.
      rewrite PurePrimops.apply_mstore_mload_diff. smt(@W256). smt(@W256).
      rewrite PurePrimops.mload_mstore_same. reflexivity.
      have H_mem6_get160: PurePrimops.mload mem_6 (W256.of_int 160) = c.
      rewrite PurePrimops.mload_mstore_same. reflexivity.
      seq 6 : (Primops.memory = mem_6 /\ x = a /\ y = b /\ z = c).
      call (ConcretePrimops.mstore_spec mem_5 (W256.of_int 160) c).
      call (ConcretePrimops.mstore_spec mem_4 (W256.of_int 128) b).
      call (ConcretePrimops.mstore_spec mem_3 (W256.of_int 96) a).
      call (ConcretePrimops.mstore_spec mem_2 (W256.of_int 64) (W256.of_int 32)).
      call (ConcretePrimops.mstore_spec mem_1 (W256.of_int 32) (W256.of_int 32)).
      call (ConcretePrimops.mstore_spec memory W256.zero (W256.of_int 32)).
      skip. by progress.
      inline Primops.staticcall.
      sp.
      rcondt 1. skip. by progress.
      rcondt 4.
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 64)).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 32)).
      call (ConcretePrimops.mload_spec mem_6 W256.zero).
      skip. progress.
      seq 6: (
        #pre /\
        bsize = W256.of_int 32 /\
        esize = W256.of_int 32 /\
        msize = W256.of_int 32 /\
        base = a /\
        exp = b /\
        mod = c
      ).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 160)).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 128)).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 96)).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 64)).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 32)).
      call (ConcretePrimops.mload_spec mem_6 W256.zero).
      skip. progress.
      pose result := (W256.of_int ((W256.to_uint a) ^ (W256.to_uint b) %% (W256.to_uint c))).
          pose mem_7 := PurePrimops.mstore mem_6 W256.zero result.
          call (ConcretePrimops.mload_spec mem_7 W256.zero).
          wp.
          call (ConcretePrimops.mstore_spec mem_6 W256.zero result).
          skip. progress.
          rewrite /mem_7.
          rewrite PurePrimops.mload_mstore_same.
          reflexivity.
      qed.


      
lemma calldata_test_correctness (ind : uint256) :
    phoare [Test.calldata_test : arg = ind ==> res = W256.one] = 1%r.
    proc.
    inline Primops.calldataload.
    wp.
    skip.
    progress.
  qed.
