require import Array Real UInt256 YulPrimops PurePrimops Utils.

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
  
lemma keccak_correctness (addr1 addr2 sz : uint256) : equiv [Primops.keccak256 ~ Primops.keccak256 : arg{1} = (addr1, sz) /\ arg{2} = (addr2, sz) /\ forall (i : uint256), W256.zero < i /\ i < sz => Primops.memory{1}.[addr1 + i] = Primops.memory{2}.[addr2 + i] ==> res{1} = res{2}].
    proc.
    while (i{1} = i{2} /\ i{1} <= sz /\ size{1} = sz /\ size{2} = sz /\ forall (j : uint256), j < i{1} => input{1}.[W256.to_uint j] = Primops.memory{1}.[off{1} + j] /\ input{2}.[W256.to_uint j] = Primops.memory{2}.[off{2} + j]).
    wp.
    skip.
    move=> &1 &2 H.
    split. split. smt ().
    split. smt (@W256).
    split. smt ().
    split. smt ().
    move=> j j_le.
    case (lt_or_eq_of_lt_succ _ _ j_le).
    progress.
    rewrite get_set_if.
    smt (@W256).
    progress.
    rewrite get_set_if.
    smt (@W256).
    move=> j_eq.
    rewrite j_eq get_set_if get_set_if.
    have H0 : 0 <= to_uint i{1}. smt (W256.to_uint_cmp).
    have H1 : 0 <= to_uint i{1}. smt (W256.to_uint_cmp).
    have H2 : to_uint i{1} = to_uint i{2}. smt ().
    split.
    simplify.
    case (0 <= to_uint i{1} && to_uint i{1} < (size input{1})%Array).
    progress.
    progress.
    admit.
    progress.
    admit.
    smt ().
    skip.
    admit.
  qed.
